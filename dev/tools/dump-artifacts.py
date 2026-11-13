#!/usr/bin/env python3
import sys
import json
import argparse
import gitlab
import time
import datetime
import dateparser
import requests
from concurrent.futures import ThreadPoolExecutor

parser = argparse.ArgumentParser()
parser.add_argument('--token', required=True, help='file containing the private token')
parser.add_argument('--until', default=None, help='only dump jobs at most this old (YYYY-MM-DD); default: full dump')
parser.add_argument('outfile', nargs='?', default='artifacts.json')
args = parser.parse_args()

with open(args.token) as tf:
    token = tf.read().strip()

gt = gitlab.Gitlab(url="https://gitlab.inria.fr", private_token=token, api_version="4")

prj = gt.projects.get("coq/coq")

oldest_date = datetime.datetime.strptime(args.until, '%Y-%m-%d') if args.until else None

PARALLEL = 4
PER_PAGE = 100

# adapter = requests.adapters.HTTPAdapter(pool_connections=PARALLEL, pool_maxsize=PARALLEL)
# gt.session.mount('https://', adapter)

def human_size(n):
    for unit in ('B', 'KiB', 'MiB', 'GiB', 'TiB'):
        if n < 1024 or unit == 'TiB':
            return f'{n:.1f}{unit}' if unit != 'B' else f'{n}B'
        n /= 1024

def fetch_page(page):
    delay = 1
    while True:
        try:
            return prj.jobs.list(scope=["failed", "success"], per_page=PER_PAGE, page=page)
        except gitlab.exceptions.GitlabHttpError as e:
            if e.response_code >= 500:
                if delay >= 60:
                    print(f'giving up on page {page} after repeated 5xx errors', file=sys.stderr)
                    raise
                time.sleep(delay)
                delay *= 2
            else:
                raise

def page_min_id(page):
    jobs = fetch_page(page)
    if not jobs:
        return None
    return min(j.id for j in jobs)

outfile = args.outfile

# ---- resume watermark: lo = oldest (smallest) job id already dumped ----
lo = None
n_existing = 0
try:
    with open(outfile) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            job = json.loads(line)
            n_existing += 1
            if lo is None or job['id'] < lo:
                lo = job['id']
except FileNotFoundError:
    pass

# ---- locate the resume page: smallest page whose min job id is <= lo ----
# pages are returned by id descending, so min_id(page) decreases as page grows
start_page = 1
if lo is not None:
    base = n_existing // PER_PAGE
    offset = 1
    while True:
        m = page_min_id(base + offset)
        if m is None or m <= lo:
            break
        offset *= 2
    if m is not None and m <= lo:
        low, high = max(base, 1), base + offset
        while low < high:
            mid = (low + high) // 2
            if page_min_id(mid) <= lo:
                high = mid
            else:
                low = mid + 1
        start_page = low
    else:
        # no page has min id <= lo: everything is already dumped
        print('everything already dumped, nothing to do')
        sys.exit(0)
    print(f'resuming from page {start_page} (lo id = {lo}, {n_existing} jobs already dumped)')

total_size = 0
total_trace = 0
n_jobs = 0

f = open(outfile, 'a' if lo is not None else 'w')
page = start_page
done = False
with ThreadPoolExecutor(max_workers=PARALLEL) as ex:
    while not done:
        futures = {ex.submit(fetch_page, page + i): page + i for i in range(PARALLEL)}
        for fut in sorted(futures, key=futures.get):
            jobs = fut.result()
            if not jobs:
                done = True
                break
            for j in jobs:
                if lo is not None and j.id >= lo:
                    continue
                jts = dateparser.parse(j.created_at).timestamp()
                if oldest_date is not None and jts < oldest_date.timestamp():
                    print('done')
                    done = True
                    break

                artifacts = j.attributes.get('artifacts', [])
                size = trace_size = 0
                for art in artifacts:
                    if art['file_type'] == 'trace':
                        trace_size += art['size']
                    else:
                        size += art['size']
                total_size += size
                total_trace += trace_size
                f.write(json.dumps({
                    'created_at': j.created_at,
                    'id': j.id,
                    'name': j.name,
                    'artifacts_size': size,
                    'trace_size': trace_size,
                }) + '\n')
                n_jobs += 1
            if done:
                break
        page += PARALLEL
f.close()

print(f'wrote {n_jobs} jobs to {outfile}, total artifacts size = {human_size(total_size)}, total trace size = {human_size(total_trace)}, total = {human_size(total_size + total_trace)}')
