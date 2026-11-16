#!/usr/bin/env python3
import argparse
import gitlab
import datetime
import dateparser

parser = argparse.ArgumentParser()
parser.add_argument('--token', required=True, help='file containing the private token')
args = parser.parse_args()

with open(args.token) as tf:
    token = tf.read().strip()

gt = gitlab.Gitlab(url="https://gitlab.inria.fr", private_token=token, api_version="4")

prj = gt.projects.get("coq/coq")

oldest_date = datetime.datetime.now() - datetime.timedelta(days=8)
newest_date = datetime.datetime.now() - datetime.timedelta(days=3)

PER_PAGE = 100

def human_size(n):
    for unit in ('B', 'KiB', 'MiB', 'GiB', 'TiB'):
        if n < 1024 or unit == 'TiB':
            return f'{n:.1f}{unit}' if unit != 'B' else f'{n}B'
        n /= 1024

def prjob(j):
    return f'{{id = {j.id}, name = {j.name}, ref = {j.ref}, created_at = {j.created_at}}}'

jobs = prj.jobs.list(ordered_by="created_at", scope=["failed", "success"], per_page=PER_PAGE, iterator=True)

cleaned_jobs = 0
cleaned_size = 0

while True:
    j = jobs.next()

    if j is None:
        print('bad done')
        break
    jts = dateparser.parse(j.created_at).timestamp()
    if jts > newest_date.timestamp():
        print(f'skip newer job {prjob(j)}')
        continue
    elif jts < oldest_date.timestamp():
        print('done')
        break

    if j.name == 'bench' or j.name.startswith('doc:'):
        print(f'skip bench or doc job {prjob(j)}')
        continue

    arts=[]
    if 'artifacts' in j.attributes:
        arts=[art for art in j.attributes['artifacts'] if art['file_type'] != 'trace']

    if len(arts) == 0:
        print(f'skip no artifacts job {prjob(j)}')
        continue

    print(f'clean {prjob(j)}, artifacts = {arts}')

    for art in arts:
        cleaned_size += art['size']
    cleaned_jobs += 1

    j.delete_artifacts()

print()
print(f'cleaned_jobs = {cleaned_jobs}, cleaned_size = {human_size(cleaned_size)}')
