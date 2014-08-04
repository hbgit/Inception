#!/usr/bin/env python
from __future__ import print_function
# -*- coding: latin1 -*-
from decorator import getfullargspec


__author__ = 'Herbert OLiveira Rocha'

#From Python
import sys
import os
import re
import commands
import csv
import inspect
from operator import itemgetter
from collections import defaultdict


# From Project
from modules.utils import datacode


#### Gather the absolute path
sys.path.append(os.path.dirname(__file__))


# -------------------------------------------------
# Global Variables
ABS_PATH = os.path.dirname(__file__)
# -------------------------------------------------

class GeneratorBmcOutput(object):
    """
    @summary: Class to parse C program to AST and then to C
    """
    def __init__(self):
        self.cprogramfile = ''
        self.current_funct = ''
        self.dictdatafunctsprog = {} # name_funct -> [line begin, line end]


        # For C file
        self.DONT_write_line_number = []        
        self.flag_assert = False
        self.flag_stdlib = False
        self.flag_stdio = False
        self.flag_stdint = False
        self.flag_others_h = False
        self.header_others = []
    

    def readCFile(self, _cfile):
        """
        Reading the source code to identify the includes that will not be write again. 
        For this we create a list to save the number of the lines identified.         
        """
        linesCFile = open(_cfile)
        self.cprogramfile = _cfile
        
        for index, eachLine in enumerate(linesCFile):
            
            matchAssertH = re.search(r'(<assert.h>)', eachLine)
            if matchAssertH:
                self.flag_assert = True
                #print("assert ",str(index+1))
                self.DONT_write_line_number.append(index+1)
                
            matchIoH = re.search(r'(<stdio.h>)', eachLine)
            if matchIoH:
                self.flag_stdio = True
                #print("io ",str(index+1))
                self.DONT_write_line_number.append(index+1)
                
            matchLibH = re.search(r'(<stdlib.h>)', eachLine)
            if matchLibH:
                self.flag_stdlib = True
                #print("lib ",str(index+1))
                self.DONT_write_line_number.append(index+1)
                
            matchIntH = re.search(r'(<stdint.h>)', eachLine)
            if matchIntH:
                self.flag_stdint = True
                #print("int ",str(index+1))
                self.DONT_write_line_number.append(index+1)
                
            matchOthersH = re.search(r'(#include.*)', eachLine)
            if matchOthersH and (not matchIntH or not matchLibH or not matchIoH or not matchAssertH):
                self.flag_others_h = True
                self.header_others.append(matchOthersH.group(1)+" \n")
            
        
        linesCFile.close()


    def generateDataFunct(self, _cprogrampath):
        """
        """
        datafunct       = datacode.DataFromCodeCtags()
        namefuncts      = datafunct.getFunctsName(_cprogrampath)
        linebeginfuncts = datafunct.getLinesBeginFunct(_cprogrampath)
        lineendfuncts   = datafunct.getLinesEndFunct(_cprogrampath)
        for index, name in enumerate(namefuncts):
            self.dictdatafunctsprog[name] = [linebeginfuncts[index],lineendfuncts[index]]


    def identifyTypeACSLAssert(self, _comment):
        type = _comment.replace("(char *)","")
        return type.replace("\"","")


    def isAssertForAll(self, _predicateAssertion):
        matchForAll = re.search(r'(__e_acsl_forall_)', _predicateAssertion)
        if matchForAll:
            return True


    def identifyEacslAssert(self, _linesprogram, index):

        # result_control[]:
        #   1st Identified a assert
        #   2st has a new line
        #   3st the new txt line
        #   4st type of assertion (RTE, PRE, POST)
        #   5st is a forall assertion
        #   6st the number of the line
        result_control = [False,False,"","",False]
        matchFunctAssert = re.search(r'e_acsl_assert\((.*)', _linesprogram[index])
        if matchFunctAssert:
            isForAll = False
            newline = ""

            get_control_elem = matchFunctAssert.group(1).split(",")
            typeassert = self.identifyTypeACSLAssert(get_control_elem[1])

            if self.isAssertForAll(get_control_elem[0]):
                isForAll = True
                result_control[4] = True

            if not isForAll:
                newline = get_control_elem[0]

            # getting the number of the line in the e-acsl asertion
            flag_getnumline = True

            while flag_getnumline:
                print(">>>>", _linesprogram[index])
                #,[ ]*([0-9]*);$
                #,0);
                matchEndAssertion = re.search(r'([0-9]*)\);$', _linesprogram[index])
                if matchEndAssertion:
                    flag_getnumline = False
                    print("MATCH:",matchEndAssertion.group(1))
                index += 1

            result_control[0] = True
            result_control[1] = not isForAll
            result_control[2] = newline
            result_control[3] = typeassert

        return result_control

            #print(">>>>>>>>", get_control_elem)



    def isNumLineBeginFunct(self, _numline):
        control_list = [False,0] #Identify if is begin funct and the num line of end funct
        for listScope in self.dictdatafunctsprog.values():
            #print(_numline,listScope[0])
            if int(_numline) == int(listScope[0]):
                control_list[0] = True
                control_list.append(int(listScope[1]))

        return control_list



    def createBmcOutput(self):

        self.generateDataFunct(self.cprogramfile)

        """
        Write the new instance of the analyzed C source code
        """
        # Check the includes and then write the nedded C headers to FORTES
        if not self.flag_assert:
            print("#include <assert.h> /** by INCEPTION **/")
        if not self.flag_stdint:
            print("#include <stdint.h> /** by INCEPTION **/")
        if not self.flag_stdio:
            print("#include <stdio.h> /** by INCEPTION **/")
        if not self.flag_stdlib:
            print("#include <stdlib.h> /** by INCEPTION **/")

        
        if self.flag_others_h:
            for header in self.header_others:
                print(header.rstrip())

        # Adding ASSERT macro
        print("#define bmc_check(predicate,line)   if(!(predicate)){ "\
              "printf(\"Invariant Violated in line: %d \\n\", line); assert(0); }")


        index = 0
        linesCFile = open(self.cprogramfile)
        list_cfile_lines = linesCFile.readlines()
        sizelistlines = len(list_cfile_lines)
        while index < sizelistlines:
            linenum = (index+1)

            control_list = self.isNumLineBeginFunct(linenum)
            # Print the functions lines in the code
            if control_list[0] :
                # Run the functions line to identify E-ACSL functions
                while (index+1) != control_list[1] and index < sizelistlines:

                    #listAssertcontrol = self.identifyEacslAssert(list_cfile_lines[index])
                    listAssertcontrol = self.identifyEacslAssert(list_cfile_lines,index)

                    # We have an assertion
                    if listAssertcontrol[0]:
                        # We have a new assertion to add
                        if listAssertcontrol[1]:
                            # TODO: o print deve ser feito de acordo com o tipo da assert
                            #print("assert( "+listAssertcontrol[2]+" );")
                            print("bmc_check( "+listAssertcontrol[2]+", "+listAssertcontrol[2]+");")
                        # Check if we have a forall assertion
                        elif listAssertcontrol[3]:
                            print("FORALL -- DOING")
                    print(list_cfile_lines[index],end="")
                    index += 1


            # Print lines of code outside of the functions
            if index < sizelistlines:
                print(list_cfile_lines[index],end="")
            index += 1


                            
        

