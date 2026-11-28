#!/usr/bin/env python3
"""Offline release checks for the public score catalogue; never contacts a server.

This checks consistency and evidence fields, not music accuracy, copyright
ownership, search-engine indexing, or whether a deployment has succeeded.
"""
from __future__ import annotations

from collections import Counter
from html.parser import HTMLParser
import importlib.util
import json
from pathlib import Path
import re
import sys
from urllib.parse import parse_qsl, unquote, urljoin, urlsplit

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SCORES = ROOT / 'scores'
ORIGIN = 'https://taitai2025.github.io'
SLUG = re.compile(r'[a-z0-9]+(?:-[a-z0-9]+)*\Z')
TEXT_TYPES = {'.html', '.js', '.mjs', '.css', '.json', '.xml', '.svg', '.md', '.py'}
PRIVATE_KEYS = {
    'password', 'passphrase', 'secret', 'token', 'accesstoken', 'refreshtoken',
    'apikey', 'privatekey', 'privateobjectkey', 'privateurl', 'signedurl',
    'authorization', 'credential', 'credentials', 'contract', 'contracttext',
    'contactemail', 'contactphone', 'revieweremail', 'private', 'internalnotes',
}
PRIVATE_QUERY = {
    'access_token', 'token', 'password', 'secret', 'authorization', 'signature',
    'x-amz-signature', 'x-amz-credential', 'x-goog-signature', 'sig',
}
SECRET_SIGNATURES = [
    (r'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----', 'private key'),
    (r'\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,})\b', 'GitHub credential'),
    (r'\bsk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{20,}\b', 'API credential'),
    (r'\bScore-[A-Za-z0-9_-]{20,}\b', 'PDF passphrase'),
]
WORK_FIELDS = {
    'title', 'version', 'slug', 'note', 'combined', 'parts', 'fullScores', 'kind',
    'composer', 'ensemble', 'tags', 'summary', 'quality', 'rights', 'rightsBasis',
    'partCount', 'priority', 'creditSource', 'movements',
}
OPEN_FIELDS = {
    'slug', 'title', 'composer', 'composerEn', 'provider', 'source', 'download',
    'edition', 'license', 'licenseUrl', 'rightsStatus', 'pages', 'volumes',
    'format', 'details', 'category', 'downloadType', 'instruments',
}
SOURCE_FIELDS = {
    'title', 'composer', 'composerEn', 'provider', 'source', 'edition', 'license',
    'licenseUrl', 'rightsStatus', 'pages', 'format', 'details', 'category',
    'access', 'accessDetail', 'evidence', 'notes', 'downloadType', 'instruments',
}
COLLECTION_FIELDS = {
    'id', 'slug', 'kind', 'title', 'url', 'composer', 'ensemble', 'format',
    'version', 'partCount', 'instruments', 'movements', 'summary', 'access',
    'quality', 'rehearsal', 'variants',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nonempty(value):
    return isinstance(value, str) and bool(value.strip())


def positive(value):
    return type(value) is int and value > 0


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'Duplicate JSON field: {key}')
        result[key] = value
    return result


def parse_json(text, label):
    try:
        return json.loads(text, object_pairs_hook=unique_object)
    except (ValueError, json.JSONDecodeError) as error:
        raise ValueError(f'{label}: {error}') from error


def load_json(relative):
    return parse_json((ROOT / relative).read_text(encoding='utf-8'), relative)


def load_assignment(relative, variable):
    text = (ROOT / relative).read_text(encoding='utf-8')
    match = re.fullmatch(r'\s*window\.' + re.escape(variable) + r'\s*=\s*(.*?)\s*;?\s*', text, re.S)
    require(match is not None, f'{relative}: expected one JSON assignment, without executable code')
    return parse_json(match.group(1), relative)


def fields(record, allowed, label):
    require(isinstance(record, dict), f'{label}: expected an object')
    extra = set(record) - allowed
    require(not extra, f'{label}: unreviewed public fields {sorted(extra)}; update the public-field allowlist deliberately')


def safe_url(value, label, *, external=False):
    require(nonempty(value), f'{label}: missing URL')
    require(not any(ord(char) < 32 for char in value) and '\\' not in value,
            f'{label}: invalid URL characters')
    parts = urlsplit(value)
    require(parts.username is None and parts.password is None, f'{label}: URL contains credentials')
    require(not ({key.lower() for key, _ in parse_qsl(parts.query)} & PRIVATE_QUERY),
            f'{label}: temporary or credential-bearing query string is not public metadata')
    if external:
        require(parts.scheme == 'https' and bool(parts.netloc), f'{label}: expected HTTPS source URL')
    elif parts.scheme:
        require(parts.scheme in {'https', 'mailto', 'tel', 'data'}, f'{label}: unsupported URL scheme')
    else:
        require(not value.startswith('//'), f'{label}: use an explicit HTTPS URL')


def check_private_data(value, label):
    if isinstance(value, dict):
        for key, item in value.items():
            normalized = re.sub(r'[^a-z0-9]', '', key.lower())
            require(normalized not in PRIVATE_KEYS, f'{label}: private field {key!r} must not enter the public build')
            check_private_data(item, label + '.' + key)
        # Machine-readable completion claims must carry an inspectable reference.
        # The reference still requires a human to verify its substance.
        if value.get('publicationStatus') in {'published', 'live', '已发布', '已部署'} or value.get('published') is True:
            require(bool(value.get('publicationEvidence')), f'{label}: published status needs publicationEvidence')
        if value.get('qualityStatus') in {'final_passed', '最终验收通过'}:
            require(bool(value.get('qualityEvidence')), f'{label}: final quality status needs qualityEvidence')
    elif isinstance(value, list):
        for index, item in enumerate(value):
            check_private_data(item, f'{label}[{index}]')
    elif isinstance(value, str):
        require(not value.startswith(('file://', 'sandbox:', 'library-file:', 'project-file:', 'oai-library://', '/workspace/')),
                f'{label}: local or private file reference is not a public URL')
        if value.startswith(('https://', 'http://', '//')):
            safe_url(value, label, external=True)


def keyed(records, label, field='slug'):
    require(isinstance(records, list), f'{label}: expected a list')
    result = {}
    for row in records:
        require(isinstance(row, dict) and nonempty(row.get(field)), f'{label}: missing {field}')
        key = row[field]
        require(key not in result, f'{label}: duplicate {field} {key}')
        if field == 'slug':
            require(SLUG.fullmatch(key), f'{label}: invalid stable ASCII slug {key!r}')
        result[key] = row
    return result


def verify_catalogue():
    works = keyed(load_json('scores/data/works.json'), 'works')
    catalog = keyed(load_assignment('scores/catalog.js', 'SCORE_CATALOG'), 'legacy catalogue')
    parts = load_assignment('scores/parts-index.js', 'SCORE_PARTS')
    rosters = load_json('scores/tools/rosters.json')
    roster_works = keyed(rosters['works'], 'instrument rosters')
    summary = keyed(load_json('scores/data.json')['works'], 'generated search index')
    for label, collection in [('legacy catalogue', catalog), ('parts index', parts),
                              ('instrument rosters', roster_works), ('search index', summary)]:
        require(set(collection) == set(works), f'{label}: work IDs differ from works.json')
    asset_count = part_count = 0
    seen_assets = set()
    for slug, work in works.items():
        label = f'work {slug}'
        fields(work, WORK_FIELDS, label)
        for key in ('title', 'version', 'ensemble', 'quality', 'rights', 'rightsBasis'):
            require(nonempty(work.get(key)), f'{label}: missing {key}; use an explicit pending status when unverified')
        require(isinstance(work.get('composer'), str), f'{label}: composer must be a string; an unknown attribution may remain empty')
        require(positive(work.get('partCount')), f'{label}: invalid partCount')
        require(type(work.get('priority')) is int and 0 <= work['priority'] <= 999, f'{label}: invalid priority')
        require(isinstance(work.get('tags'), list) and all(nonempty(x) for x in work['tags']), f'{label}: invalid tags')
        for group in ('combined', 'parts', 'fullScores'):
            require(isinstance(work.get(group), list), f'{label}: missing {group} list')
            require(work[group] == catalog[slug].get(group), f'{label}: legacy {group} links differ from current version')
            for asset in work[group]:
                fields(asset, {'label', 'bytes', 'url', 'pages', 'count', 'sha256'}, f'{label}/{group}')
                require(nonempty(asset.get('label')) and positive(asset.get('bytes')), f'{label}/{group}: invalid label or byte length')
                measure = 'count' if group == 'parts' else 'pages'
                require(positive(asset.get(measure)), f'{label}/{group}: invalid {measure}')
                url = asset.get('url')
                safe_url(url, f'{label}/{group}', external=True)
                prefix = 'https://github.com/Taitai2025/taitai2025.github.io/releases/download/'
                require(url.startswith(prefix), f'{label}/{group}: unreviewed delivery host; update the explicit allowlist when changing delivery provider')
                require(url not in seen_assets, f'{label}/{group}: duplicate release asset')
                seen_assets.add(url)
                suffix = '.zip' if group == 'parts' else '.pdf'
                require(urlsplit(url).path.endswith(suffix), f'{label}/{group}: expected {suffix} asset')
                if 'sha256' in asset:
                    require(re.fullmatch(r'[0-9a-f]{64}', asset['sha256']), f'{label}/{group}: invalid SHA-256')
                asset_count += 1
        require(catalog[slug]['version'] == work['version'], f'{label}: legacy version differs')
        require(sum(row['count'] for row in work['parts']) == work['partCount'], f'{label}: ZIP count differs')
        filenames = set()
        for row in parts[slug]:
            fields(row, {'filename', 'pages'}, f'{label}/part')
            name = row.get('filename')
            require(nonempty(name) and name.endswith('.pdf') and '/' not in name and '\\' not in name,
                    f'{label}: invalid part filename')
            require(name not in filenames and positive(row.get('pages')), f'{label}: duplicate part filename or invalid page count')
            filenames.add(name)
        require(len(filenames) == work['partCount'] == summary[slug]['partCount'], f'{label}: catalogue/filename/search counts differ')
        require(nonempty(roster_works[slug].get('title')) and roster_works[slug].get('lines'), f'{label}: missing instrument roster')
        require((SCORES / 'work' / slug / 'index.html').is_file(), f'{label}: detail page has not been generated')
        part_count += len(filenames)
    sources = load_json('scores/data/sources.json')
    require(set(sources) == {'openScores', 'sources'}, 'sources.json: unexpected root fields')
    opens = keyed(sources['openScores'], 'open editions')
    require(not (set(opens) & set(works)), 'Open and protected edition slugs overlap')
    for slug, edition in opens.items():
        label = f'open edition {slug}'
        fields(edition, OPEN_FIELDS, label)
        for key in ('title', 'edition', 'provider', 'license', 'rightsStatus'):
            require(nonempty(edition.get(key)), f'{label}: missing {key}')
        if 'downloadType' in edition:
            require(edition['downloadType'] in {'pdf', 'zip'}, f'{label}: invalid downloadType')
        if 'instruments' in edition:
            require(isinstance(edition['instruments'], list) and all(nonempty(x) for x in edition['instruments']), f'{label}: invalid instrument labels')
        require(positive(edition.get('pages')), f'{label}: invalid page count')
        for key in ('source', 'download'):
            safe_url(edition.get(key), f'{label}/{key}', external=True)
        if edition.get('licenseUrl'):
            safe_url(edition['licenseUrl'], f'{label}/licenseUrl', external=True)
        for volume in edition.get('volumes', []):
            fields(volume, {'volume', 'label', 'scanPages', 'source', 'download'}, f'{label}/volume')
            bounds = volume.get('scanPages')
            require(isinstance(bounds, list) and len(bounds) == 2 and all(positive(x) for x in bounds) and bounds[0] <= bounds[1], f'{label}: invalid scan page range')
            safe_url(volume.get('download'), f'{label}/volume/download', external=True)
        require((SCORES / 'open' / slug / 'index.html').is_file(), f'{label}: missing detail page')
    for index, source in enumerate(sources['sources']):
        label = f'external source {index + 1}'
        fields(source, SOURCE_FIELDS, label)
        for key in ('title', 'access'):
            require(nonempty(source.get(key)), f'{label}: missing {key}')
        safe_url(source.get('source'), label, external=True)
    for label, data in [('catalogue', catalog), ('parts', parts), ('rosters', rosters)]:
        check_private_data(data, label)
    collection_path = SCORES / 'collection-index.json'
    if collection_path.is_file():
        collection = load_json('scores/collection-index.json')
        require(set(collection) == {'schemaVersion', 'records'} and collection['schemaVersion'] == 1,
                'collection-index.json: unsupported schema')
        records = keyed(collection['records'], 'programme collection', field='id')
        expected_ids = {'work:' + slug for slug in works} | {'open:' + slug for slug in opens}
        require(set(records) == expected_ids, 'Programme collection differs from the current work and open-edition catalogues')
        for identifier, record in records.items():
            fields(record, COLLECTION_FIELDS, identifier)
            prefix, slug = identifier.split(':', 1)
            require(record['slug'] == slug and nonempty(record.get('title')), f'{identifier}: wrong slug or title')
            require(record.get('url') == f'/scores/{prefix}/{slug}/', f'{identifier}: incorrect detail URL')
            for key in ('instruments', 'movements', 'variants'):
                require(isinstance(record.get(key), list) and all(nonempty(x) for x in record[key]),
                        f'{identifier}: invalid {key}')
            if prefix == 'work':
                require(record.get('partCount') == works[slug]['partCount'], f'{identifier}: stale part count')
    return len(works), len(opens), len(sources['sources']), asset_count, part_count


class Document(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.references = []
        self.ids = []
        self.base = None
        self.feed(text)

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if attrs.get('id'):
            self.ids.append(attrs['id'])
        if tag == 'base':
            self.base = attrs.get('href')
        if tag in {'a', 'link', 'script', 'img', 'source', 'audio', 'video', 'iframe', 'form'}:
            for key in ('src', 'href', 'action', 'poster'):
                if attrs.get(key):
                    self.references.append(attrs[key])


def local_target(reference, source, base=None):
    safe_url(reference, source.relative_to(ROOT).as_posix())
    if reference.startswith(('data:', 'mailto:', 'tel:')):
        return None
    origin = ORIGIN + '/' + source.relative_to(ROOT).as_posix()
    address = urlsplit(urljoin(urljoin(origin, base or ''), reference))
    if address.netloc != urlsplit(ORIGIN).netloc:
        return None
    relative = unquote(address.path).lstrip('/')
    require('\x00' not in relative and '\\' not in relative, 'Invalid local path')
    target = (ROOT / relative).resolve()
    require(target.is_relative_to(ROOT), f'{source.relative_to(ROOT)}: link escapes project root')
    if target.is_dir():
        target /= 'index.html'
    require(target.is_file(), f'{source.relative_to(ROOT)}: missing local target {address.path}')
    return target, address.fragment


def verify_references():
    documents = {file.resolve(): Document(file.read_text(encoding='utf-8')) for file in SCORES.rglob('*.html')}
    checked = 0
    for path, document in documents.items():
        duplicates = [key for key, count in Counter(document.ids).items() if count > 1]
        require(not duplicates, f'{path.relative_to(ROOT)}: duplicate HTML IDs {duplicates}')
        for reference in document.references:
            target = local_target(reference, path, document.base)
            if target and target[1] and target[0] in documents:
                fragment = unquote(target[1])
                if not fragment.startswith(':~:text='):
                    require(fragment in documents[target[0]].ids,
                            f'{path.relative_to(ROOT)}: missing static anchor {target[0].relative_to(ROOT)}#{fragment}')
            checked += 1
    for path in sorted(SCORES.rglob('*')):
        if path.suffix == '.css':
            references = re.findall(r'url\(\s*[\'"]?([^\'"\)]+)[\'"]?\s*\)', path.read_text(encoding='utf-8'))
        elif path.suffix in {'.js', '.mjs'}:
            references = re.findall(r'(?:\bfrom\s*|\bimport\s*(?:\(\s*)?)[\'"](\.{1,2}/[^\'"]+)[\'"]', path.read_text(encoding='utf-8'))
        else:
            continue
        for reference in references:
            if not reference.startswith('#'):
                local_target(reference, path)
                checked += 1
    return len(documents), checked


def check_sensitive_text(text, label):
    for pattern, description in SECRET_SIGNATURES:
        require(not re.search(pattern, text), f'{label}: possible {description}; matched values are intentionally hidden')


def verify_public_files():
    count = 0
    for path in sorted(SCORES.rglob('*')):
        if not path.is_file():
            continue
        require(not path.is_symlink(), f'{path.relative_to(ROOT)}: symlinks are not public catalogue assets')
        require(not path.name.startswith('.env') and path.name not in {'id_rsa', 'id_ed25519'}, f'{path.relative_to(ROOT)}: private file')
        if path.suffix not in TEXT_TYPES:
            continue
        text = path.read_text(encoding='utf-8')
        check_sensitive_text(text, str(path.relative_to(ROOT)))
        if path.suffix == '.json':
            check_private_data(parse_json(text, str(path.relative_to(ROOT))), str(path.relative_to(ROOT)))
        count += 1
    return count


def verify():
    counts = verify_catalogue()
    pages, references = verify_references()
    files = verify_public_files()
    specification = importlib.util.spec_from_file_location('score_discovery', ROOT / 'scripts/check-score-discovery.py')
    discovery = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(discovery)
    routes, root_routes = discovery.verify(ROOT, False)
    return {
        'works': counts[0], 'openEditions': counts[1], 'externalSources': counts[2],
        'releaseAssets': counts[3], 'indexedParts': counts[4], 'htmlFiles': pages,
        'staticReferences': references, 'publicTextFiles': files,
        'scoreSitemapRoutes': routes, 'rootSitemapRoutes': root_routes,
        'deploymentVerified': False,
    }


if __name__ == '__main__':
    try:
        result = verify()
    except (ValueError, OSError, KeyError, TypeError) as error:
        raise SystemExit(f'Score validation failed: {error}') from error
    print('PASS: public catalogue, asset counts, static links, data boundaries and sitemap discovery')
    print(json.dumps(result, ensure_ascii=False, indent=2))
    print('Offline checks do not certify copyright, musical accuracy, or a live deployment.')
