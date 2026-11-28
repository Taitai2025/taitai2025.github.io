#!/usr/bin/env python3
"""Validate static links, canonical URLs, and both score-site sitemaps."""
from argparse import ArgumentParser
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urljoin, urlsplit
from urllib.request import urlopen
from xml.etree import ElementTree

ORIGIN = "https://taitai2025.github.io"
SCORE_HOME = ORIGIN + "/scores/"
LOC = "{http://www.sitemaps.org/schemas/sitemap/0.9}loc"


class Page(HTMLParser):
    def __init__(self, url, text):
        super().__init__()
        self.url = self.base = url
        self.hrefs = []
        self.canonicals = []
        self.robots = ""
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        data = dict(attrs)
        href = data.get("href")
        if tag == "base" and href:
            self.base = urljoin(self.url, href)
        elif tag == "a" and href:
            self.hrefs.append(href)
        elif tag == "link" and data.get("rel") == "canonical" and href:
            self.canonicals.append(href)
        elif tag == "meta" and data.get("name") == "robots":
            self.robots = data.get("content", "").lower()

    def links(self):
        for href in self.hrefs:
            yield urlsplit(urljoin(self.base, href))._replace(query="", fragment="").geturl()


def locations(text, title):
    entries = [item.text for item in ElementTree.fromstring(text).iter(LOC)]
    urls = set(entries)
    if None in urls or len(urls) != len(entries):
        raise ValueError(f"{title} contains missing or duplicate URLs")
    return urls


def fetched_text(url):
    with urlopen(url, timeout=14) as reply:
        if reply.status != 200 or reply.geturl() != url:
            raise ValueError(f"{url} must return a direct HTTP 200")
        if "noindex" in reply.headers.get("X-Robots-Tag", "").lower():
            raise ValueError(f"{url} uses an HTTP noindex header")
        return reply.read().decode("utf-8")


def score_pages(root, urls, live):
    if live:
        def fetch(url):
            return url, Page(url, fetched_text(url))
        with ThreadPoolExecutor(max_workers=8) as workers:
            return dict(workers.map(fetch, sorted(urls)))
    loaded = {}
    for file in sorted((root / "scores").rglob("index.html")):
        url = ORIGIN + "/" + file.parent.relative_to(root).as_posix() + "/"
        loaded[url] = Page(url, file.read_text(encoding="utf-8"))
    return loaded


def reachable(home, pages):
    queue = deque(home.links())
    seen = set()
    while queue:
        url = queue.popleft()
        if url in pages and url not in seen:
            seen.add(url)
            queue.extend(pages[url].links())
    return seen


def verify(root, live):
    def read(relative):
        if live:
            return fetched_text(ORIGIN + "/" + relative.removesuffix("index.html"))
        return (root / relative).read_text(encoding="utf-8")

    robots_lines = read("robots.txt").splitlines()
    for route in ("sitemap.xml", "scores/sitemap.xml"):
        if f"Sitemap: {ORIGIN}/{route}" not in robots_lines:
            raise ValueError(f"robots.txt must announce /{route}")
    sitemap = locations(read("scores/sitemap.xml"), "Score sitemap")
    root_map = locations(read("sitemap.xml"), "Root sitemap")
    if SCORE_HOME not in sitemap or not all(url.startswith(SCORE_HOME) for url in sitemap):
        raise ValueError("The score sitemap must include the score home and only score-site routes")
    if any(url.startswith(SCORE_HOME) and url not in sitemap for url in root_map):
        raise ValueError("A root map score URL is missing from the score sitemap")
    pages = score_pages(root, sitemap, live)
    expected = {url for url, page in pages.items() if "noindex" not in page.robots}
    if expected != sitemap:
        raise ValueError(f"Map coverage: missing {sorted(expected-sitemap)}; unexpected {sorted(sitemap-expected)}")
    for url in sorted(expected):
        if pages[url].canonicals != [url]:
            raise ValueError(f"{url} must have exactly one self-referencing canonical")
    home = Page(ORIGIN + "/", read("index.html"))
    if SCORE_HOME not in home.links():
        raise ValueError("The personal home needs a static score-site link")
    missed = sitemap - reachable(home, pages)
    if missed:
        raise ValueError(f"No static path from the home page: {sorted(missed)}")
    return len(sitemap), len(root_map)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--live", action="store_true", help="Verify the released site over HTTPS")
    args = parser.parse_args()
    try:
        score, total = verify(Path(__file__).resolve().parent.parent, args.live)
    except (ValueError, OSError, ElementTree.ParseError) as error:
        raise SystemExit(f"Score discovery check: {error}") from error
    print(f"PASS: {score} canonical score pages, {total} root sitemap URLs, two map declarations and a static homepage link")
