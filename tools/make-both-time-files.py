#!/usr/bin/env python3
from TimeFileMaker import *

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=r'''Formats timing information from the output of two invocations of `make TIMED=1` into a sorted table.''')
    add_sort_by(parser)
    add_json(parser)
    add_real(parser)
    add_include_mem(parser)
    add_sort_by_mem(parser)
    add_after_file_name(parser)
    add_before_file_name(parser)
    add_output_file_name(parser)
    args = parser.parse_args()
    if args.json:
        get_file_times = (lambda f: get_times_and_mems_from_trace(f, use_real=args.real, include_mem=args.include_mem))
    else:
        get_file_times = (lambda f: get_times_and_mems(f, use_real=args.real, include_mem=args.include_mem))
    left_dict = get_file_times(args.AFTER_FILE_NAME)
    right_dict = get_file_times(args.BEFORE_FILE_NAME)
    table = make_diff_table_string(left_dict, right_dict, sort_by=args.sort_by, include_mem=args.include_mem, sort_by_mem=args.sort_by_mem)
    print_or_write_table(table, args.OUTPUT_FILE_NAME)
