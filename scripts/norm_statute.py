"""Script to normalize a text file.

This script is useful for cleaning up and standardizing the appearance of
statute text.  The script expects each paragraph to be separated by a
single blank line.  The script was tested with Python 3.4.

Usage:

    $ python scripts/norm_statute.py PATH

"""

# TODO: have the script leave the "header" information alone, perhaps with
# some type of marker text to indicate the start of the actual statute text.

import textwrap
import sys


ENCODING = 'utf-8'
WIDTH = 72


def normalize_spaces(line):
    """Replace substrings of whitespace with a single space."""
    return " ".join(line.split())


def main(argv):
    args = argv[1:]
    path = args[0]

    with open(path, encoding=ENCODING) as f:
        text = f.read()

    paras = text.split("\n\n")

    paras = [textwrap.fill(normalize_spaces(para), width=WIDTH) for para in paras]

    text = "\n\n".join(paras)
    # Ensure the file ends in a newline.
    text += "\n"

    with open(path, encoding=ENCODING, mode='w') as f:
        f.write(text)


if __name__ == '__main__':
    main(sys.argv)
