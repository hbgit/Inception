#!/usr/bin/env python
from __future__ import print_function
# -*- coding: latin1 -*-
from decorator import getfullargspec

__author__ = 'Herbert OLiveira Rocha'


#From python
import commands
import sys
import re



class DataFromCodeCtags(object):

    def __init__(self):
        self.cprogramfile = ''
        self.list_functions_start_line_num = []
        self.list_functions_end_line_num = []


    def getFunctsName(self, _cprogrampath):
        """
        Get the name of the functions and the
        line number where it begin

        :param _cprogrampath:
        :return:
        """

        grep_name = "grep -o \"^[^ ]*\" "
        functions_name = commands.getoutput("ctags --sort=NO -x --c-kinds=f "+ _cprogrampath +" | "+grep_name).split("\n")

        return functions_name


    def getLinesBeginFunct(self,_cprogrampath):
        """
        Get the number of the line where each function begin
        :param _cprogrampath:
        :return:
        """
        grep_lines = "grep -o \"function[ ]*[0-9][^ ]*\""
        rec_lines = commands.getoutput("ctags --sort=NO -x --c-kinds=f "+ _cprogrampath + " | " +grep_lines).split("\n")

        for line in rec_lines:
            # Isolating rvalue from assignment
            matchOnlyNum = re.search(r'(.[^ ]*$)', line)
            if matchOnlyNum:
                self.list_functions_start_line_num.append(matchOnlyNum.group(1).strip())


        return self.list_functions_start_line_num


    def getLinesEndFunct(self,_cprogrampath):
        """

        :param _cprogrampath:
        :return:
        """
        for index, num in enumerate(self.list_functions_start_line_num):
            #print(num+" --- ", end="")
            getEndLineFunction = commands.getoutput("awk \'NR > first && /^}$/ { print NR; exit }\' first="+
                                                    num+" "+ _cprogrampath)
            self.list_functions_end_line_num.append(getEndLineFunction)
        return self.list_functions_end_line_num





