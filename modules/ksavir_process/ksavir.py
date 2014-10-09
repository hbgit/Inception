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



class DtraceProcess(object):

    def __init__(self):
        self.actualindexfile = 0

    def preprocess_dtrace_file(self, _dtracepath):
        newdtracefile = open("test.dtrace",'w')

        with open(_dtracepath) as f:
            for line in f:
                txtline = str(line)
                matchskipcontrolpoints = re.search(r'(.*:::.*)', txtline)
                if matchskipcontrolpoints:
                    newdtracefile.write(txtline)
                    #print("<<<<<<<"+txtline, end="")
                else:
                    #newdtracefile.write(txtline+"########")
                    matchreptxt = re.search(r'(.*::.[^:]*)', txtline)
                    if matchreptxt:
                        #print("########"+txtline.replace("::",""), end="")
                        newline = txtline.replace("::","")
                        newdtracefile.write(newline)
                    else:
                        #print("########"+txtline, end="")
                        newdtracefile.write(txtline)


        newdtracefile.close()