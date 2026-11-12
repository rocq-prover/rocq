#!/usr/bin/env python3
import json
import re
import argparse
from collections import OrderedDict
from tabulate import tabulate

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', default='artifacts.json')
parser.add_argument('--time-bucketing', choices=['day', 'month', 'year'], default=None, help='bucket by day, month or year; default: auto (month if >=3 distinct months, else day)')
parser.add_argument('--before', default=None, help='only consider jobs created on/before this date (YYYY-MM-DD, inclusive)')
parser.add_argument('--after', default=None, help='only consider jobs created on/after this date (YYYY-MM-DD, inclusive)')
parser.add_argument('--name', default=None, help='only consider jobs whose name matches this regex')
args = parser.parse_args()

name_re = re.compile(args.name) if args.name else None

def human_size(n):
    for unit in ('B', 'KiB', 'MiB', 'GiB', 'TiB'):
        if n < 1024 or unit == 'TiB':
            return f'{n:.1f}{unit}' if unit != 'B' else f'{n}B'
        n /= 1024

per_name = {}
per_day = OrderedDict()
total_trace = 0
total_jobs = 0
months = set()
seen = set()
with open(args.infile) as f:
    for line in f:
        line = line.strip()
        if not line:
            continue
        job = json.loads(line)
        if job['id'] in seen:
            continue
        seen.add(job['id'])
        if name_re is not None and not name_re.search(job['name']):
            continue
        # created_at is ISO 8601, e.g. "2026-11-12T14:34:48.000Z"
        date = job['created_at'][:10]
        if args.before is not None and date > args.before:
            continue
        if args.after is not None and date < args.after:
            continue
        n, nart, ntrace = per_name.get(job['name'], (0, 0, 0))
        per_name[job['name']] = (n + 1, nart + job['artifacts_size'], ntrace + job['trace_size'])
        n, art, trace = per_day.get(date, (0, 0, 0))
        per_day[date] = (n + 1, art + job['artifacts_size'], trace + job['trace_size'])
        total_trace += job['trace_size']
        total_jobs += 1
        months.add(date[:7])

bucket = args.time_bucketing or ('month' if len(months) >= 3 else 'day')
BUCKET_LEN = {'day': 10, 'month': 7, 'year': 4}
per_time = OrderedDict()
for date, (n, art, trace) in per_day.items():
    key = date[:BUCKET_LEN[bucket]]
    cn, cart, ctrace = per_time.get(key, (0, 0, 0))
    per_time[key] = (cn + n, cart + art, ctrace + trace)

name_rows = [[name, n, human_size(art), human_size(trace), human_size(art + trace)]
             for name, (n, art, trace)
             in sorted(per_name.items(), key=lambda kv: kv[1][1] + kv[1][2])]

print('By job name')
print()
print(tabulate(name_rows, headers=['name', 'jobs', 'artifacts size', 'logs size', 'total'],
               tablefmt='pipe', colalign=('left', 'right', 'right', 'right', 'right')))

time_rows = [[key, n, human_size(art), human_size(trace), human_size(art + trace)]
             for key, (n, art, trace) in reversed(list(per_time.items()))]

print()
print(f'By {bucket}')
print()
print(tabulate(time_rows, headers=[bucket, 'jobs', 'artifacts size', 'logs size', 'total'],
               tablefmt='pipe', colalign=('left', 'right', 'right', 'right', 'right')))

print()
total_art = sum(a for _, a, _ in per_name.values())
print(f'total jobs = {total_jobs}, total artifacts = {human_size(total_art)}, total logs = {human_size(total_trace)}, total = {human_size(total_art + total_trace)}')
print(f'average log size per day = {human_size(total_trace // len(per_day)) if per_day else 0}')
