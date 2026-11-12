import gitlab
import datetime
import dateparser

gt = gitlab.Gitlab(url="https://gitlab.inria.fr", private_token=REDACTED, api_version="4")

prj = gt.projects.get("coq/coq")

jobs = prj.jobs.list(ordered_by="created_at", scope=["failed", "success"], iterator=True)

oldest_date = datetime.datetime.now() - datetime.timedelta(days=30)
newest_date = datetime.datetime.now() - datetime.timedelta(days=7)

def prjob(j):
    return f'{{id = {j.id}, name = {j.name}, ref = {j.ref}, created_at = {j.created_at}}}'

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
print(f'cleaned_jobs = {cleaned_jobs}, cleaned_size = {cleaned_size}B')
