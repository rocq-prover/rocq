##########################################################################
##         #      The Rocq Prover / The Rocq Development Team           ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""
Drive rocq top with Python!
=========================

This module is a simple pexpect-based driver for rocq top, based on the old
REPL interface.
"""

import os
import re
import tempfile

import pexpect


class RocqTopError(Exception):
    def __init__(self, err, last_sentence, before):
        super().__init__()
        self.err = err
        self.before = before
        self.last_sentence = last_sentence

class RocqTop:
    """Create an instance of rocq top.

    Use this as a context manager: no instance of rocq top is created until
    you call `__enter__`.  rocq top is terminated when you `__exit__` the
    context manager.

    Sentence parsing is very basic for now (a "." in a quoted string will
    confuse it).

    When environment variable ROCQ_DEBUG_REFMAN is set, all the input
    we send to rocq top is copied to a temporary file "/tmp/rocqdomainXXXX.v".
    """

    ROCQTOP_PROMPT = re.compile("\r\n[^< \r\n]+ < ")

    def __init__(self, rocqbin=None, color=False, args=None) -> str:
        """Configure a rocq top instance (but don't start it yet).

        :param rocqbin:    The path to rocq; uses $COQBIN by default, falling
                           back to "rocq"
        :param color:      When True, tell "rocq top" to produce ANSI color
                           codes (see the ansicolors module)
        :param args:       Additional arguments to "rocq top".
        """
        self.rocqbin = rocqbin or os.path.join(os.getenv("COQBIN", ""), "rocq")
        if not pexpect.utils.which(self.rocqbin):
            raise ValueError("'{}: not found".format(rocqbin))
        self.args = ["top"] + (args or []) + ["-q"] + ["-color", "on"] * color
        self.rocqtop = None
        self.debugfile = None

    def __enter__(self):
        if self.rocqtop:
            raise ValueError("This module isn't re-entrant")
        self.rocqtop = pexpect.spawn(self.rocqbin, args=self.args, echo=False, encoding="utf-8")
        # Disable delays (http://pexpect.readthedocs.io/en/stable/commonissues.html?highlight=delaybeforesend)
        self.rocqtop.delaybeforesend = 0
        if os.getenv ("ROCQ_DEBUG_REFMAN"):
            self.debugfile = tempfile.NamedTemporaryFile(mode="w+", prefix="rocqdomain", suffix=".v", delete=False, dir="/tmp/")
        self.next_prompt()
        return self

    def __exit__(self, type, value, traceback):
        if self.debugfile:
            self.debugfile.close()
            self.debugfile = None
        self.rocqtop.kill(9)

    def next_prompt(self):
        """Wait for the next rocq top prompt, and return the output preceding it."""
        self.rocqtop.expect(RocqTop.ROCQTOP_PROMPT, timeout = 10)
        return self.rocqtop.before

    def sendone(self, sentence):
        """Send a single sentence to rocq top.

        :sentence: One Rocq sentence (otherwise, rocq top will produce multiple
                   prompts and we'll get confused)
        """
        # Suppress newlines, but not spaces: they are significant in notations
        sentence = re.sub(r"[\r\n]+", " ", sentence).strip()
        try:
            if self.debugfile:
                self.debugfile.write(sentence+"\n")
            self.rocqtop.sendline(sentence)
            output = self.next_prompt()
        except Exception as err:
            raise RocqTopError(err, sentence, self.rocqtop.before)
        return output

    def send_initial_options(self):
        """Options to send when starting the toplevel and after a Reset Initial."""
        self.sendone('Set Rocqtop Exit On Error.')
        self.sendone('Set Warnings "+default".')

def sendmany(*sentences):
    """A small demo: send each sentence in sentences and print the output"""
    with RocqTop() as rocqtop:
        for sentence in sentences:
            print("=====================================")
            print(sentence)
            print("-------------------------------------")
            response = rocqtop.sendone(sentence)
            print(response)

def main():
    """Run a simple performance test and demo `sendmany`"""
    with RocqTop() as rocqtop:
        for _ in range(200):
            print(repr(rocqtop.sendone("Check nat.")))
        sendmany("Goal False -> True.", "Proof.", "intros H.",
                 "Check H.", "Chchc.", "apply I.", "Qed.")

if __name__ == '__main__':
    main()
