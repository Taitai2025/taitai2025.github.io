#!/usr/bin/env python3
"""Build only the orchestra showcase, or validate its documented source data."""
import argparse
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from orchestra_showcase import build_showcase, load_data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Validate data and image/source references without writing pages')
    args = parser.parse_args()
    if args.check:
        entries = load_data()
        print(f'Validated {len(entries)} orchestra(s), {sum(len(item["gallery"]) for item in entries)} gallery images and {sum(len(item["videos"]) for item in entries)} performance links.')
        return
    path = Path(__file__).with_name('build-score-site.py')
    spec = importlib.util.spec_from_file_location('showcase_site_api', path)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    routes = build_showcase(api)
    print('Built showcase routes: ' + ', '.join(routes))


if __name__ == '__main__':
    main()
