#!/usr/bin/env python
from __future__ import print_function
# -*- coding: latin1 -*-

__author__ = 'Herbert OLiveira Rocha'
FRAMEWORK_VERSION = 'version 1'


# From python
import argparse
import sys
import os
import commands
import re
import csv
import shutil
from pipes import quote
from operator import itemgetter

# From inception
from modules.eacsl_to_esbmc import generate_esbmc_output


# -------------------------------------------------
# Class to run inception
# -------------------------------------------------

class Inception(object):

    def __init__(self):
        self.ABS_PATH = os.path.dirname(__file__)
        self.cprogram_path = ""


    def generate_bmc_output(self, _cprogrampath):
        #print(_cprogrampath)
        insertInstr = generate_esbmc_output.GeneratorBmcOutput()
        insertInstr.readCFile(_cprogrampath)
        insertInstr.createBmcOutput()




# -------------------------------------------------
# Main python program
# -------------------------------------------------

if __name__ == "__main__":

    ############# Parse args options
    parser = argparse.ArgumentParser(description='Running Inception v1')
    parser.add_argument('-v','--version', action='version' , version="version 1")
    parser.add_argument(dest='inputCProgram', metavar='file.c', type=str,
               help='the C program file to be analyzed')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('-e','--e-acsl-output', action="store_true" , dest='setEacslOutput',
               help='Adding assertion based on E-ACSL ouput', default=False)

    args = parser.parse_args()

    ## ------------ Check options in the args
    # vars to save data option

    if args.inputCProgram:
        if not os.path.isfile(args.inputCProgram):
            print('Error: unable to open input file (%s)' % args.inputCProgram)
            parser.parse_args(['-h'])
            sys.exit()

    if args.setEacslOutput:
        run = Inception()
        run.cprogram_path = os.path.abspath(args.inputCProgram)
        run.generate_bmc_output(run.cprogram_path)
        # TODO: add a post preprocessing code





