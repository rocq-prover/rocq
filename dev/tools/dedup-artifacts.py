#!/usr/bin/env python3
import os
import sys
import json
import argparse
import tempfile

parser = argparse.ArgumentParser(description='remove duplicate job ids from a dump, keeping the first record for each id')
parser.add_argument('infile', nargs='?', default='artifacts.json')
parser.add_argument('outfile', nargs='?', default=None, help='output file (default: overwrite infile)')
args = parser.parse_args()

outfile = args.outfile or args.infile

seen = set()
fd, tmp = tempfile.mkstemp(dir=os.path.dirname(outfile) or '.', suffix='.dedup')
try:
    with open(args.infile) as fin, os.fdopen(fd, 'w') as fout:
        for line in fin:
            line = line.strip()
            if not line:
                continue
            job = json.loads(line)
            if job['id'] in seen:
                continue
            seen.add(job['id'])
            fout.write(json.dumps(job) + '\n')
    os.replace(tmp, outfile)
except Exception:
    os.unlink(tmp)
    raise

print(f'wrote {len(seen)} unique jobs to {outfile}')
