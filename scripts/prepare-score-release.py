#!/usr/bin/env python3
"""Prepare a reviewable score-site delta without committing, pushing or deploying.

Uses a temporary Git index, so the real staging area is unchanged. All bundled
files are read from one captured Git tree. Keep output outside the checkout.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
EXACT_PATHS = {
    'index.html', 'about/index.html', 'research/index.html', 'notes/index.html',
    'robots.txt', 'sitemap.xml', 'package.json', 'README.md',
    '.github/workflows/score-validation.yml',
    'scripts/build-static.cjs', 'scripts/build-score-site.py',
    'scripts/check-score-discovery.py', 'scripts/verify-score-site.py',
    'scripts/prepare-score-release.py', 'scripts/score_experience.py',
    'scripts/test-arrange-comparison.mjs', 'scripts/test-arrange-project.mjs',
    'scripts/test-catalogue.py', 'scripts/test-experience.mjs',
    'scripts/build-orchestra-showcase.py', 'scripts/orchestra_showcase.py',
    'scripts/test-orchestra-showcase.mjs', 'scripts/score_community.py',
    'scores/orchestras/intake-template.txt',
}
MUSIC_IMAGE_EXTENSIONS = {'.jpg', '.jpeg', '.png', '.webp', '.avif'}
PUBLIC_EXTENSIONS = {
    '.html', '.css', '.js', '.mjs', '.json', '.svg', '.xml', '.md',
    '.woff', '.woff2', '.png', '.jpg', '.jpeg', '.webp', '.avif', '.ico',
}


def git(*arguments, env=None, text=True, stdin=None):
    result = subprocess.run(['git', *arguments], cwd=ROOT, env=env, capture_output=True, input=stdin)
    if result.returncode:
        raise ValueError(f'Local Git command failed: {arguments[0]} (exit {result.returncode})')
    return result.stdout.decode('utf-8') if text else result.stdout


def allowed(path):
    parsed = PurePosixPath(path)
    if parsed.is_absolute() or '..' in parsed.parts or any(ord(char) < 32 for char in path):
        return False
    if path in EXACT_PATHS or path == 'scores/tools/build_rosters.py':
        return True
    if path.startswith('scripts/test-score-') and parsed.suffix in {'.mjs', '.py'}:
        return True
    if path.startswith('assets/images/music/') and parsed.suffix in MUSIC_IMAGE_EXTENSIONS:
        return not any(part.startswith('.') for part in parsed.parts)
    return path.startswith('scores/') and parsed.suffix in PUBLIC_EXTENSIONS and not any(part.startswith('.') for part in parsed.parts)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def working_fingerprint():
    paths = set(EXACT_PATHS)
    paths.update(str(path.relative_to(ROOT)) for path in (ROOT / 'scores').rglob('*') if path.is_file())
    paths.update(str(path.relative_to(ROOT)) for path in (ROOT / 'scripts').glob('test-score-*'))
    paths.update(str(path.relative_to(ROOT)) for path in (ROOT / 'assets/images/music').rglob('*') if path.is_file() and path.suffix in MUSIC_IMAGE_EXTENSIONS)
    result = {}
    for name in sorted(paths):
        path = ROOT / name
        if path.is_file():
            if path.is_symlink():
                raise ValueError(f'Symlink is not a release file: {name}')
            result[name] = digest(path.read_bytes())
    return result


def load_validator():
    specification = importlib.util.spec_from_file_location('score_validation', ROOT / 'scripts/verify-score-site.py')
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def prepare(base, output):
    output = output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError('Release output must be outside the Git checkout')
    baseline = git('rev-parse', '--verify', '--end-of-options', base + '^{commit}').strip()
    head = git('rev-parse', 'HEAD').strip()
    changed = set(filter(None, git('diff', '--name-only', '--no-renames', '-z', baseline, '--').split('\0')))
    changed.update(filter(None, git('ls-files', '--others', '--exclude-standard', '-z').split('\0')))
    if not changed:
        raise ValueError('No changes relative to the requested baseline')
    excluded = sorted(path for path in changed if not allowed(path))
    if excluded:
        raise ValueError('Changes outside the score release allowlist; review them in a separate checkout:\n' + '\n'.join(excluded))
    before = working_fingerprint()
    validator = load_validator()
    check = validator.verify()
    test = subprocess.run(['npm', 'run', 'check:scores'], cwd=ROOT, capture_output=True, text=True)
    if test.returncode:
        raise ValueError('Score regression checks failed; run npm run check:scores for details')
    for name in sorted(before):
        if name.startswith('scores/') and Path(name).suffix in {'.js', '.mjs'}:
            syntax = subprocess.run(['node', '--check', name], cwd=ROOT, capture_output=True)
            if syntax.returncode:
                raise ValueError(f'JavaScript syntax check failed: {name}')
    with tempfile.TemporaryDirectory(prefix='guoyue-release-index-') as temp:
        env = {**os.environ, 'GIT_INDEX_FILE': str(Path(temp) / 'index')}
        git('read-tree', baseline, env=env)
        git('add', '-A', '--', *sorted(changed), env=env)
        tree = git('write-tree', env=env).strip()
        statuses = git('diff', '--cached', '--name-status', '--no-renames', '-z', baseline, '--', env=env).split('\0')
        rows = []
        files = {}
        for position in range(0, len(statuses) - 1, 2):
            status, name = statuses[position:position + 2]
            if status not in {'A', 'M', 'D'}:
                raise ValueError(f'Unsupported release change {status}: {name}')
            if not allowed(name):
                raise ValueError(f'Unreviewed release path: {name}')
            row = {'path': name, 'change': status}
            if status != 'D':
                mode = git('ls-tree', tree, '--', name, env=env).split(' ', 1)[0]
                if mode not in {'100644', '100755'}:
                    raise ValueError(f'Non-regular release entry: {name}')
                content = git('show', tree + ':' + name, env=env, text=False)
                if Path(name).suffix in validator.TEXT_TYPES | {'.yml', '.yaml'}:
                    validator.check_sensitive_text(content.decode('utf-8'), name)
                files[name] = content
                row.update({'bytes': len(content), 'sha256': digest(content), 'mode': mode})
            rows.append(row)
        patch = git('diff', '--cached', '--binary', '--full-index', '--no-ext-diff', baseline, '--', env=env, text=False)
        git('read-tree', baseline, env=env)
        git('apply', '--cached', '--check', '-', env=env, stdin=patch)
        git('apply', '--cached', '-', env=env, stdin=patch)
        if git('write-tree', env=env).strip() != tree:
            raise ValueError('Patch replay differs from the captured source tree')
    if working_fingerprint() != before:
        raise ValueError('Source changed while the release was being checked; wait for edits to finish and retry')
    for name, content in files.items():
        if digest(content) != before.get(name):
            raise ValueError(f'Git filters changed {name}; review the stored bytes before preparing a release')
    timestamp = datetime.now(timezone.utc)
    manifest = {
        'format': 1, 'status': 'prepared',
        'createdAtUTC': timestamp.isoformat(timespec='seconds'),
        'targetOrigin': 'https://taitai2025.github.io',
        'baselineCommit': baseline, 'sourceHead': head, 'snapshotTree': tree,
        'realIndexModified': False, 'patchReplayVerified': True, 'patchSha256': digest(patch), 'checks': check,
        'deployment': {'verified': False, 'deployedCommit': None, 'deploymentUrl': None},
        'files': rows,
    }
    readme = '''# 国乐谱汇待发布增量包

本包只表示源码及离线检查已准备完成，不表示已提交或已上线。

## 内容

- `upload/`：新增或修改文件，保留仓库相对路径。
- `release.patch`：相对于 manifest 中 baselineCommit 的完整二进制兼容补丁。
- `manifest.json`：基线、快照树、逐文件路径/变更类型/大小/SHA-256、检查范围。
- `SHA256SUMS`：上传文件与补丁的校验和。

## 发布

先核对远端 main 是否仍为 baselineCommit；有新提交时，在最新远端上合并并重新检查，不能覆盖其他会话的研究或网站更新。

用已授权的 GitHub 网页或 Git 客户端，将 upload 中的文件放到完全相同的仓库路径。浏览器上传不会自动展开 ZIP；不要把本 ZIP 当网页文件提交。manifest 中 change=D 的条目需单独删除，不能遗留旧网页。先在开发分支检查 diff，核对路径、文件数、公开数据与删除项，再合并发布。

有 Git 客户端时，可在正确基线的隔离分支运行 `git apply --check release.patch`，再应用补丁；本包不是带作者信息的 git-format-patch，不使用 git am。

保留实际提交 SHA 和 GitHub Pages 成功部署记录。等待发布后执行 `npm run check:scores:live`，再人工核对首页、曲目详情、搜索、编制工具及真实下载。只有以上线上证据齐全，才把维护记录改为“已上线并核验”。

## 回退

记录上一成功部署对应的提交。若发布有问题，优先撤销本次明确提交并正常推送，使 Pages 重新发布；不要 force-push 或覆盖其他人的提交。回退后重做线上检查。删除变更只能按清单还原，不能整站删库再上传。

## 边界

本包不包含 GitHub 凭据、私有台账或谱件密码；公开 Release 链接保留在既有目录中。校验是离线一致性与公开边界检查，不是音乐逐音校勘、版权认定、搜索收录证明或支付系统验收。
'''
    checksums = ''.join(f'{row["sha256"]}  upload/{row["path"]}\n' for row in rows if row['change'] != 'D')
    checksums += digest(patch) + '  release.patch\n'
    payloads = {
        **{'upload/' + path: content for path, content in files.items()},
        'manifest.json': (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode('utf-8'),
        'release.patch': patch,
        'SHA256SUMS': checksums.encode('utf-8'),
        'README_RELEASE.md': readme.encode('utf-8'),
    }
    name = 'guoyue-release-' + timestamp.strftime('%Y%m%dT%H%M%SZ') + '-' + tree[:12]
    directory = output / name
    directory.mkdir(parents=True, exist_ok=False)
    for relative, content in payloads.items():
        target = directory / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    archive = output / (name + '.zip')
    with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as bundle:
        for relative in sorted(payloads):
            bundle.writestr(relative, payloads[relative])
    with zipfile.ZipFile(archive) as bundle:
        if bundle.testzip() is not None:
            raise ValueError('Release ZIP failed its CRC check')
        for row in rows:
            if row['change'] != 'D' and digest(bundle.read('upload/' + row['path'])) != row['sha256']:
                raise ValueError('Release ZIP failed its file digest check')
    return {
        'status': 'prepared', 'archive': str(archive), 'directory': str(directory),
        'archiveSha256': digest(archive.read_bytes()), 'snapshotTree': tree,
        'files': len(rows), 'deletions': sum(row['change'] == 'D' for row in rows),
        'deploymentVerified': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True, help='Reviewed baseline commit; verify it against the latest remote before publishing')
    parser.add_argument('--output', required=True, type=Path, help='Destination directory outside this checkout')
    args = parser.parse_args()
    try:
        result = prepare(args.base, args.output)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        raise SystemExit(f'Release preparation failed: {error}') from error
    print(json.dumps(result, ensure_ascii=False, indent=2))
