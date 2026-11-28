#!/usr/bin/env python3
"""Copy already password-protected score PDFs from verified Release ZIPs."""
from argparse import ArgumentParser
from hashlib import file_digest, sha256
import json
import os
from pathlib import Path, PurePosixPath
import re
from shutil import copyfile
import stat
from subprocess import PIPE, run
from tempfile import TemporaryDirectory
from time import sleep
from urllib.error import URLError
from urllib.parse import urlsplit
from urllib.request import Request, urlopen
from zipfile import ZipFile

import fitz


ORIGIN = "https://github.com/Taitai2025/taitai2025.github.io.git"
API = "https://api.github.com/repos/Taitai2025/taitai2025.github.io"
RELEASE = "https://github.com/Taitai2025/taitai2025.github.io/releases/download"
BRANCH = "refs/heads/score-pdf-files"
MANIFEST = "scores/data/direct-parts.json"
MIB = 1024 ** 2
BATCH_LIMIT = 420 * MIB
PUSH_MAX = 450 * MIB
MAX_PDF = 100 * MIB
TAG = r"minyue-jianpu-\d{8}"
HEX_DIGEST = re.compile(r"[a-f0-9]{64}")
USER_AGENT = "Taitai2025 score catalogue publication"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fetch(url):
    return urlopen(Request(url, headers={"User-Agent": USER_AGENT}), timeout=120)


def read_json(url):
    with fetch(url) as response:
        return json.load(response)


def member_path(name):
    require("\\" not in name and all(p not in ("", ".", "..") for p in name.split("/")),
            "Unsafe ZIP member path")
    return PurePosixPath(name).name


def catalogue(root, selection):
    works = json.loads((root / "scores/data/works.json").read_text(encoding="utf-8"))
    raw = (root / "scores/parts-index.js").read_text(encoding="utf-8")
    prefix = "window.SCORE_PARTS = "
    require(raw.startswith(prefix), "Unexpected parts-index.js format")
    pages = json.loads(raw[len(prefix):].strip().removesuffix(";"))
    slugs = {work["slug"] for work in works}
    require(len(slugs) == len(works), "Duplicate work slug")
    require(selection <= slugs, f"Unknown work selection: {', '.join(sorted(selection - slugs))}")
    labels = {}
    for work in works:
        slug = work["slug"]
        if selection and slug not in selection:
            continue
        require(re.fullmatch(r"[a-z0-9-]+", slug), f"Invalid slug: {slug}")
        rows = pages[slug]
        labels[slug] = {row["filename"]: row["pages"] for row in rows}
        require(len(labels[slug]) == len(rows) == work["partCount"], f"Bad part index: {slug}")
        require(all(member_path(name) == name and name.lower().endswith(".pdf") and
                    type(n) is int and n > 0 for name, n in labels[slug].items()),
                f"Invalid part index rows: {slug}")
    return [work for work in works if work["slug"] in labels], labels


def release_sources(works):
    releases = {}
    sources = {}
    for work in works:
        slug = work["slug"]
        assets = []
        for entry in work["parts"]:
            pattern = rf"{re.escape(RELEASE)}/({TAG})/({re.escape(slug)}-parts-\d{{2}}\.zip)"
            match = re.fullmatch(pattern, entry["url"])
            require(match, f"Unexpected official archive URL for {slug}")
            tag, name = match.groups()
            if tag not in releases:
                detail = read_json(f"{API}/releases/tags/{tag}")
                require(detail["tag_name"] == tag and not detail["draft"], f"Invalid release {tag}")
                releases[tag] = {a["name"]: a for a in detail["assets"]}
            official = releases[tag][name]
            digest = official.get("digest", "").removeprefix("sha256:")
            require(HEX_DIGEST.fullmatch(digest), f"GitHub digest unavailable for {name}")
            require(official["state"] == "uploaded" and official["browser_download_url"] == entry["url"],
                    f"Release asset differs for {name}")
            require(official["size"] == entry["bytes"] and 0 < official["size"] < 2 * 1024 * MIB,
                    f"Release asset size differs for {name}")
            require(entry.get("sha256", digest) == digest, f"Catalogue digest differs for {name}")
            assets.append((entry, f"{tag}-{digest[:16]}", digest))
        require(assets and sum(a[0]["count"] for a in assets) == work["partCount"],
                f"Invalid Release part counts for {slug}")
        sources[slug] = assets
    return sources


def archive_bytes(asset, digest, target):
    h = sha256()
    size = 0
    with fetch(asset["url"]) as response, target.open("wb") as file:
        final = urlsplit(response.url)
        require(final.scheme == "https" and final.hostname == "release-assets.githubusercontent.com",
                "Unexpected Release asset host")
        while chunk := response.read(MIB):
            size += len(chunk)
            require(size <= asset["bytes"], "Release archive exceeded listed size")
            h.update(chunk)
            file.write(chunk)
    require(size == asset["bytes"] and h.hexdigest() == digest, "Release ZIP digest or size differs")


def approved_pdf(data, expected_pages):
    require(data.startswith(b"%PDF-"), "ZIP member is not a PDF")
    with fitz.open(stream=data, filetype="pdf") as document:
        require(document.needs_pass and document.is_encrypted and
                document.xref_get_key(-1, "Encrypt")[0] in ("xref", "dict"),
                "ZIP member does not require a PDF open password")
        require(not document.is_repaired, "Damaged PDF requires repair")
        require(document.page_count == expected_pages, "PDF page count differs from catalogue")


def stage_work(slug, assets, expected, scratch):
    staged = {}
    for asset, edition, digest in assets:
        local_zip = scratch / "source.zip"
        archive_bytes(asset, digest, local_zip)
        with ZipFile(local_zip) as zip_file:
            files = [i for i in zip_file.infolist() if not i.is_dir() and
                     i.filename.lower().endswith(".pdf")]
            require(len(files) == asset["count"], f"Wrong PDF member count for {slug}")
            require(len(files) < 10000, f"Too many PDF members for {slug}")
            for index, member in enumerate(files, 1):
                name = member_path(member.filename)
                require(name in expected and name not in staged, f"Unexpected or duplicate part for {slug}: {name}")
                require(0 < member.file_size <= MAX_PDF and not member.flag_bits & 1 and
                        not stat.S_ISLNK(member.external_attr >> 16), f"Unsupported member for {slug}: {name}")
                data = zip_file.read(member)
                try:
                    approved_pdf(data, expected[name])
                except ValueError as err:
                    raise ValueError(f"{slug}/{name}: {err}") from err
                path = f"parts/{slug}/{edition}/{index:04}.pdf"
                output = scratch / path
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(data)
                staged[name] = {
                    "path": path, "sha256": sha256(data).hexdigest(),
                    "pages": expected[name], "bytes": len(data),
                }
        local_zip.unlink()
    require(staged.keys() == expected.keys(), f"Release PDFs differ from the part index for {slug}")
    return staged


class AssetBranch:
    def __init__(self, directory, token):
        self.directory = directory
        self.env = {key: value for key, value in os.environ.items() if key != "SCORE_ASSET_PUSH_TOKEN"}
        self.env["GIT_TERMINAL_PROMPT"] = "0"
        self.push_env = None
        self.git("init", "-q")
        self.git("remote", "add", "origin", ORIGIN)
        self.git("config", "remote.origin.promisor", "true")
        self.git("config", "remote.origin.partialclonefilter", "blob:none")
        self.git("config", "user.name", "github-actions[bot]")
        self.git("config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
        if token:
            askpass = directory / "askpass"
            askpass.write_text('#!/bin/sh\ncase "$1" in\n  *Username*) printf "%s\\n" x-access-token;;\n  *) printf "%s\\n" "$SCORE_ASSET_PUSH_TOKEN";;\nesac\n')
            askpass.chmod(0o700)
            self.push_env = dict(self.env, GIT_ASKPASS=str(askpass), SCORE_ASSET_PUSH_TOKEN=token)
        self.tip = self.git("ls-remote", "origin", BRANCH).split("\t", 1)[0]
        if self.tip:
            self.git("fetch", "--no-tags", "--depth=1", "--filter=blob:none", "origin", BRANCH)
            self.tip = self.git("rev-parse", "FETCH_HEAD")
            self.git("read-tree", self.tip)
            self.members = {}
            records = self.git("ls-tree", "-r", "-z", self.tip, trim=False)
            for row in records.split("\0"):
                if row:
                    identity, path = row.split("\t", 1)
                    self.members[path] = identity.split()[2]
        else:
            self.members = {}
        self.manifest = (json.loads(self.git("show", f"{self.tip}:{MANIFEST}"))
                         if MANIFEST in self.members else {})
        self.pending = 0

    def git(self, *args, stdin=None, env=None, trim=True):
        proc = run(["git", *args], cwd=self.directory, input=stdin, text=True, stdout=PIPE,
                   check=True, env=self.env if env is None else env)
        return proc.stdout.strip() if trim else proc.stdout

    def indexed(self, slug, assets, expected):
        rows = self.manifest.get(slug, {})
        counts = {edition: asset["count"] for asset, edition, _ in assets}
        paths = {f"parts/{slug}/{edition}/{i:04}.pdf"
                 for edition, count in counts.items() for i in range(1, count + 1)}
        return (rows.keys() == expected.keys() and
                {row.get("path") for row in rows.values()} == paths and
                paths <= self.members.keys() and
                all(row.get("pages") == expected[name] and
                    type(row.get("bytes")) is int and 0 < row["bytes"] <= MAX_PDF and
                    HEX_DIGEST.fullmatch(row.get("sha256", "")) for name, row in rows.items()))

    def add(self, path, file):
        size = file.stat().st_size
        if self.pending + size > BATCH_LIMIT:
            self.commit("Pack password-protected score PDFs")
        oid = self.git("hash-object", "-w", "--", str(file))
        if path in self.members:
            require(self.members[path] == oid, f"Versioned path collision: {path}")
        else:
            self.set_blob(path, oid)
            self.pending += size

    def set_blob(self, path, oid):
        self.git("update-index", "--add", "--cacheinfo", "100644", oid, path)
        self.members[path] = oid

    def commit(self, message):
        if not self.pending:
            return
        tree = self.git("write-tree")
        parents = ["-p", self.tip] if self.tip else []
        after = self.git("commit-tree", tree, *parents, "-m", message)
        # Validate the actual packed object size. Disable deltas while estimating;
        # the push may choose deltas against already uploaded objects.
        revisions = after + "\n" + (f"^{self.tip}\n" if self.tip else "")
        with TemporaryDirectory(dir=self.directory) as directory:
            pack = Path(directory) / "transfer.pack"
            with pack.open("wb") as file:
                run(["git", "pack-objects", "--stdout", "--revs", "--window=0"],
                    cwd=self.directory, input=revisions.encode("ascii"), stdout=file,
                    env=self.env, check=True)
            size = pack.stat().st_size
        require(size <= PUSH_MAX, "Computed git push pack exceeded 450 MiB")
        self.git("push", "origin", f"{after}:{BRANCH}", env=self.push_env)
        self.tip = after
        self.pending = 0
        print(f"Pushed asset branch {after[:12]} ({size / MIB:.1f} MiB pack bound)", flush=True)

    def verify_delivery(self, row):
        end = min(127, row["bytes"] - 1)
        url = f"https://raw.githubusercontent.com/Taitai2025/taitai2025.github.io/{self.tip}/{row['path']}"
        origin = "https://taitai2025.github.io"
        request = Request(url, headers={"User-Agent": USER_AGENT, "Origin": origin, "Range": f"bytes=0-{end}"})
        for delay in (0, 2, 5, 10):
            if delay:
                sleep(delay)
            try:
                with urlopen(request, timeout=20) as response:
                    if (response.status == 206 and
                            response.headers.get("Access-Control-Allow-Origin") in ("*", origin) and
                            response.headers.get("Content-Range") == f"bytes 0-{end}/{row['bytes']}" and
                            response.read(end + 2).startswith(b"%PDF-")):
                        return
            except URLError:
                continue
        raise ValueError("Published PDF did not pass the raw host CORS and Range check")

    def publish_manifest(self, old_manifest, scratch):
        if self.manifest == old_manifest:
            return
        target = scratch / "direct-parts.json"
        data = json.dumps(self.manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
        target.write_text(data, encoding="utf-8")
        self.set_blob(MANIFEST, self.git("hash-object", "-w", "--", str(target)))
        self.pending += len(data.encode("utf-8"))
        self.commit("Update direct score part manifest")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--slugs", default="", help="Comma-separated checked-in work slugs. Empty selects all.")
    parser.add_argument("--output", help="Write a local asset tree instead of pushing.")
    parser.add_argument("--root", default=Path(__file__).resolve().parents[1], type=Path,
                        help="Catalogue source checkout.")
    args = parser.parse_args()
    token = os.environ.get("SCORE_ASSET_PUSH_TOKEN", "")
    require(args.output or token, "A write token is required for GitHub publication")
    selection = {slug.strip() for slug in args.slugs.split(",") if slug.strip()}
    works, expected = catalogue(args.root, selection)
    sources = release_sources(works)
    with TemporaryDirectory(prefix="score-raw-branch-") as directory:
        branch = None if args.output else AssetBranch(Path(directory), token)
        if branch:
            reset_manifest = dict(branch.manifest)
        else:
            output = Path(args.output) / MANIFEST
            reset_manifest = json.loads(output.read_text(encoding="utf-8")) if output.exists() else {}
        manifest = dict(reset_manifest)
        samples = []
        for work in works:
            slug = work["slug"]
            if branch and branch.indexed(slug, sources[slug], expected[slug]):
                print(f"{slug}: verified current published index; skipped", flush=True)
                continue
            with TemporaryDirectory(prefix="score-part-pack-") as temp:
                source = Path(temp)
                parts = stage_work(slug, sources[slug], expected[slug], source)
                for row in parts.values():
                    path = row["path"]
                    if branch:
                        branch.add(path, source / path)
                    else:
                        target = Path(args.output) / path
                        target.parent.mkdir(parents=True, exist_ok=True)
                        if target.exists():
                            with target.open("rb") as file:
                                require(file_digest(file, "sha256").hexdigest() == row["sha256"],
                                        f"Versioned path collision: {path}")
                        else:
                            with TemporaryDirectory(dir=target.parent) as location:
                                partial = Path(location) / "part.pdf"
                                copyfile(source / path, partial)
                                partial.replace(target)
                manifest[slug] = parts
                samples.append(next(iter(parts.values())))
                print(f"{slug}: verified {len(parts)} password-protected PDFs", flush=True)
        if branch:
            branch.commit("Pack password-protected score PDFs")
            if samples:
                branch.verify_delivery(samples[0])
            branch.manifest = manifest
            branch.publish_manifest(reset_manifest, Path(directory))
        else:
            output = Path(args.output) / MANIFEST
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
