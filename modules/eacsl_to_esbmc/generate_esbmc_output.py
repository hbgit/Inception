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
from modules.bmcs.esbmc import esbmc_option


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
        self.list_num_lines_cl = [] # to identify the claims in the ESBMC --show-claims
        self.listlinesnotwrite = []


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
        #print(_predicateAssertion)
        matchForAll = re.search(r'(e_acsl_forall)', _predicateAssertion)
        if matchForAll:
            #print("YES")
            return True
        else:
            #print("NO")
            return False


    def identifyEacslAssert(self, _linesprogram, index):

        # result_control[]:
        #   1st Identified a assert
        #   2st has a new line
        #   3st the new txt line
        #   4st type of assertion (RTE, PRE, POST)
        #   5st is a forall assertion
        #   6st the number of the line
        result_control = [False,False,"","",False,0]
        matchFunctAssert = re.search(r'e_acsl_assert\((.*)', _linesprogram[index])
        if matchFunctAssert:
            self.listlinesnotwrite.append(index)
            isForAll = False
            newline = ""

            get_control_elem = matchFunctAssert.group(1).split(",")
            typeassert = self.identifyTypeACSLAssert(get_control_elem[1])

            #TODO: If it was a RTE assert we need modify the number of line shown by e-acsl, cuz
            #      always is 0 << we need to improve this

            #print(index)
            if self.isAssertForAll(get_control_elem[0]):
                isForAll = True
                result_control[4] = True


            if not isForAll:
                newline = get_control_elem[0]

            # getting the number of the line in the e-acsl asertion
            flag_getnumline = True
            linenumassert = 0
            while flag_getnumline:
                #print(">>>>", _linesprogram[index])
                #,[ ]*([0-9]*);$
                #,0);
                matchEndAssertion = re.search(r'([0-9]*)\);$', _linesprogram[index])
                if matchEndAssertion:
                    flag_getnumline = False
                    #print("MATCH:",matchEndAssertion.group(1))
                    linenumassert = matchEndAssertion.group(1).strip()
                index += 1

            result_control[0] = True
            result_control[1] = not isForAll
            result_control[2] = newline
            result_control[3] = typeassert
            result_control[5] = linenumassert

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


    def generate_list_of_num_assert(self, _list_identifiers):
        listnumline = []
        for index, data in enumerate(_list_identifiers):
            if data:
                listnumline.append(index+1)
        return listnumline



    def createBmcOutput(self, _bmc_tool_path):

        self.generateDataFunct(self.cprogramfile)
        # 1st list - the code;
        # 2st list - Identifier if the line is a new assert
        # 3st list - The number of the line in the original related to the assert pointed out
        list_newcodetobmc = [[],[],[]]
        listposadded_forall = []

        """
        Write the new instance of the analyzed C source code
        """

        #TODO: adding this header in the end of the generation
        # Check the includes and then write the nedded C headers to FORTES
        # if not self.flag_assert:
        #     #list_newcodetobmc.append("#include <assert.h> /** by INCEPTION **/ \n")
        #     print("#include <assert.h> /** by INCEPTION **/")
        # #if not self.flag_stdint:
        # #    print("#include <stdint.h> /** by INCEPTION **/")
        # if not self.flag_stdio:
        #     #list_newcodetobmc.append("#include <stdio.h> /** by INCEPTION **/ \n")
        #     print("#include <stdio.h> /** by INCEPTION **/")
        #if not self.flag_stdlib:
        #    print("#include <stdlib.h> /** by INCEPTION **/")

        
        # if self.flag_others_h:
        #     for header in self.header_others:
        #         #list_newcodetobmc.append(header.rstrip())
        #         print(header.rstrip())


        # # Adding ASSERT macro
        # list_newcodetobmc[0].append(
        #     "#define BMC_CHECK(predicate,line)   if(!(predicate)){ "
        #     "printf(\"Invariant Violated in line: %d \\n\", line); assert(0); } \n"
        # )
        # list_newcodetobmc[1].append(False)

        # Comments in the top of the file
        list_newcodetobmc[0].append("/* Updated by Inception */ \n")
        list_newcodetobmc[1].append(False)



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

                    #list_newcodetobmc.append(str(index)+" << in FUNC \n")
                    #print(flag_from_forall)

                    # We have an assertion
                    if listAssertcontrol[0]:
                        # We have a new assertion to add
                        if listAssertcontrol[1]:
                            #print("assert( "+listAssertcontrol[2]+" );")
                            # TODO: if the type of assert is Precondition translate to ASSUME
                            # list_newcodetobmc[0].append("BMC_CHECK( "+listAssertcontrol[2]+", "+listAssertcontrol[5]+"); \n")
                            list_newcodetobmc[0].append("assert( " + listAssertcontrol[2] + "); \n")
                            list_newcodetobmc[1].append(True)
                            list_newcodetobmc[2].append(listAssertcontrol[5])

                            #print("BMC_CHECK( "+listAssertcontrol[2]+", "+listAssertcontrol[5]+"); \n")
                            # Check if is comming from forall in this case we plus 2 == 2 new asserts added

                            #to_script = str(len(list_newcodetobmc))+";"+str(listAssertcontrol[5])
                            #self.list_num_lines_cl.append(to_script)
                            #print("BMC_CHECK( "+listAssertcontrol[2]+", "+listAssertcontrol[5]+");")

                        # Check if we have a forall assertion
                        elif listAssertcontrol[3]:
                            # generating assert to forall
                            # From FORALL assertion running the code to bottom-up to find "if(predicate)" x2 and stop
                            # in the while(1)
                            flag_from_forall = True

                            counttostopwhile = 0
                            # Cuz we run in partial and new code that has been generated
                            actualposinnewcode = len(list_newcodetobmc[0]) - 1
                            actualposinnewcode -= 1 # before FORALL

                            while counttostopwhile < 2:

                                matchIfsInForAll = re.search(r'if[ ]*\((.*)\)', list_newcodetobmc[0][actualposinnewcode])
                                if matchIfsInForAll:
                                    #listposadded_forall.append(actualpos)
                                    counttostopwhile += 1
                                    # TODO: generate assertion to new code
                                    # identifying if the list of new code was modified
                                    # Question: Does the actualpos is less than
                                    #           all elements in the listposadded_forall?
                                    # pos2addinlist = actualpos
                                    # for elemt in listposadded_forall:
                                    #     if actualpos >= elemt:
                                    #         pos2addinlist = actualpos + len(listposadded_forall)
                                    #         break
                                    #list_newcodetobmc.append("if in: "+str(actualpos)+"-> "+list_cfile_lines[actualpos]+"\n")
                                    # list_newcodetobmc[0].insert(actualposinnewcode, "BMC_CHECK( " + matchIfsInForAll.group(1)
                                    #                             + " , " + listAssertcontrol[5] + "); \n")
                                    list_newcodetobmc[0].insert(actualposinnewcode, "assert( " + matchIfsInForAll.group(1) + "); \n")
                                    list_newcodetobmc[1].insert(actualposinnewcode, True)
                                    list_newcodetobmc[2].append(listAssertcontrol[5])

                                    #print(">>>>>", actualposinnewcode)

                                    #to_script = str(len(list_newcodetobmc))+";"+str(listAssertcontrol[5])
                                    #self.list_num_lines_cl.append(to_script)

                                    #list_newcodetobmc.insert(pos2addinlist, "NEW FOR ALL \n")
                                    #list_newcodetobmc.insert(actualpos, "NEW FOR ALL \n")
                                    #print(matchIfsInForAll.group(1),"    ::   ", listAssertcontrol[5])
                                actualposinnewcode -= 1

                            # Como inserir os elemts na lista sem perder a proxima referencia
                            #print(listposadded_forall)
                            #list_newcodetobmc.append("//FORALL -- DOING \n")
                            #print("//FORALL -- DOING")


                    #list_newcodetobmc.append(str(index)+" << in FUNC "+list_cfile_lines[index])
                    if index in self.listlinesnotwrite:
                        flagstopendline = False
                        while not flagstopendline:
                            matchendline = re.search(r'[;]$', list_cfile_lines[index].strip())
                            if matchendline:
                                flagstopendline = True
                                #list_newcodetobmc[0].append(">>>"+list_cfile_lines[index])
                            index += 1
                    else:
                        list_newcodetobmc[0].append(list_cfile_lines[index])
                        list_newcodetobmc[1].append(False)
                        index += 1


            # Print lines of code outside of the functions
            if index < sizelistlines:
                #list_newcodetobmc.append(str(index)+" << GLOBAL \n")
                #list_newcodetobmc.append(str(index)+" << GLOBAL "+list_cfile_lines[index])
                list_newcodetobmc[0].append(list_cfile_lines[index])
                list_newcodetobmc[1].append(False)
                #print(list_cfile_lines[index],end="")
                index += 1 # BUG


        # Generate name to save the new code
        newnametocode = self.cprogramfile.replace(".c","__incep_annot.c")


        # Print the new code
        linesCFile = open(newnametocode, "w")

        for index, line in enumerate(list_newcodetobmc[0]):
            linesCFile.write(line)
            #print(line,end="")

        linesCFile.close()

        #STOP: Create a method to identify the lines where we added an assertion in list_newcodetobmc[1]
        listlinenumassert = self.generate_list_of_num_assert(list_newcodetobmc[1])

        # Generating the script to check the assert added to BMC
        #1) --show-claims
        runbmc = esbmc_option.EsbmcRun()
        listofbmcclaims = runbmc.generate_claims(newnametocode,_bmc_tool_path)

        #2) identify claims based on self.list_num_lines_cl[0]
        # Generating a list only with line num from assert added
        listbmcnumcl = runbmc.get_claims_from_lines(listlinenumassert,listofbmcclaims)

        #3) generate script based on result of step 2
        runbmc.write_esbmc_script(newnametocode,listbmcnumcl,list_newcodetobmc[2])




        #for i in self.list_num_lines_cl:
        #    print(i)
        

