#!/usr/bin/env python
from __future__ import print_function
# -*- coding: latin1 -*-

__author__ = 'Herbert OLiveira Rocha'

#Python
import sys
import os
import re
import csv
import inspect
from operator import itemgetter
from collections import defaultdict

# From PycParser
import pycparser.c_parser
import pycparser.c_ast
from pycparser.c_ast import *
import pycparser.c_generator


#### Gather the absolute path
sys.path.append(os.path.dirname(__file__))


# -------------------------------------------------
# Global Variables
# Portable cpp path for Windows and Linux/Unix
CPPPATH = '../utils/cpp.exe' if sys.platform == 'win32' else 'cpp'
ABS_PATH = os.path.dirname(__file__)
# -------------------------------------------------

class MyCGenerator(object):
    """ Uses the same visitor pattern as c_ast.NodeVisitor, but modified to
        return a value from each visit method, using string accumulation in
        generic_visit.
    """
    def __init__(self):
        self.output = ''

        # Statements start with indentation of self.indent_level spaces, using
        # the _make_indent method
        #
        self.indent_level = 0 
        self.test = ParseC2Ast2C()
    

    def _make_indent(self):
        return ' ' * self.indent_level

    def visit(self, node):
        method = 'visit_' + node.__class__.__name__
        return getattr(self, method, self.generic_visit)(node)
            
    def generic_visit(self, node):
        #~ print('generic:', type(node))
        if node is None:
            return ''
        else:            
            return ''.join(self.visit(c) for c in node.children())

    def visit_Constant(self, n):
        return n.value

    def visit_ID(self, n):
        return n.name

    def visit_ArrayRef(self, n):
        arrref = self._parenthesize_unless_simple(n.name)
        return arrref + '[' + self.visit(n.subscript) + ']'

    def visit_StructRef(self, n):
        sref = self._parenthesize_unless_simple(n.name)
        return sref + n.type + self.visit(n.field)

    def visit_FuncCall(self, n):
        fref = self._parenthesize_unless_simple(n.name)
        return fref + '(' + self.visit(n.args) + ')'

    def visit_UnaryOp(self, n):
        operand = self._parenthesize_unless_simple(n.expr)
        if n.op == 'p++':
            return '%s++' % operand
        elif n.op == 'p--':
            return '%s--' % operand
        elif n.op == 'sizeof':
            # Always parenthesize the argument of sizeof since it can be
            # a name.
            return 'sizeof(%s)' % self.visit(n.expr)
        else:
            return '%s%s' % (n.op, operand)

    def visit_BinaryOp(self, n):
        lval_str = self._parenthesize_if(n.left,
                            lambda d: not self._is_simple_node(d))
        rval_str = self._parenthesize_if(n.right,
                            lambda d: not self._is_simple_node(d))
        return '%s %s %s' % (lval_str, n.op, rval_str)

    def visit_Assignment(self, n):
        rval_str = self._parenthesize_if(
                            n.rvalue,
                            lambda n: isinstance(n, Assignment))
        return '%s %s %s' % (self.visit(n.lvalue), n.op, rval_str)

    def visit_IdentifierType(self, n):
        return ' '.join(n.names)

    def visit_Decl(self, n, no_type=False):
        # no_type is used when a Decl is part of a DeclList, where the type is
        # explicitly only for the first delaration in a list.
        #
        s = n.name if no_type else self._generate_decl(n)
        
        if n.bitsize: s += ' : ' + self.visit(n.bitsize)
        if n.init:
            if isinstance(n.init, InitList):
                s += ' = {' + self.visit(n.init) + '}'
            elif isinstance(n.init, ExprList):
                s += ' = (' + self.visit(n.init) + ')'
            else:
                s += ' = ' + self.visit(n.init)
        # New FORTES
        #if 'extern' in n.storage:            
            #s += '; \n'
            #return s
        #else:            
            #return s

    def visit_DeclList(self, n):
        s = self.visit(n.decls[0])
        if len(n.decls) > 1:
            s += ', ' + ', '.join(self.visit_Decl(decl, no_type=True)
                                    for decl in n.decls[1:])
        return s

    def visit_Typedef(self, n):
        s = ''
        if n.storage: s += ' '.join(n.storage) + ' '
        s += self._generate_type(n.type)
        return s

    def visit_Cast(self, n):
        s = '(' + self._generate_type(n.to_type) + ')'
        return s + ' ' + self._parenthesize_unless_simple(n.expr)

    def visit_ExprList(self, n):
        visited_subexprs = []
        for expr in n.exprs:
            if isinstance(expr, ExprList):
                visited_subexprs.append('(' + self.visit(expr) + ')')
            else:
                visited_subexprs.append(self.visit(expr))
        return ', '.join(visited_subexprs)

    def visit_InitList(self, n):
        visited_subexprs = []
        for expr in n.exprs:
            if isinstance(expr, ExprList):
                visited_subexprs.append('(' + self.visit(expr) + ')')
            elif isinstance(expr, InitList):
                visited_subexprs.append('{' + self.visit(expr) + '}')
            else:
                visited_subexprs.append(self.visit(expr))
        return ', '.join(visited_subexprs)

    def visit_Enum(self, n):
        s = 'enum'
        if n.name: s += ' ' + n.name
        if n.values:
            s += ' {'
            for i, enumerator in enumerate(n.values.enumerators):
                s += enumerator.name
                if enumerator.value:
                    s += ' = ' + self.visit(enumerator.value)
                if i != len(n.values.enumerators) - 1:
                    s += ', '
            s += '}'
        return s

    def visit_FuncDef(self, n):          
        
        decl = self.visit(n.decl)
        self.indent_level = 0
        body = self.visit(n.body)
        if n.param_decls:
            knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
            return decl + '\n' + knrdecls + ';\n' + body + '\n'
        else:
            return decl + '\n' + body + '\n'

    def visit_FileAST(self, n):
        s = ''
        for ext in n.ext:
            if isinstance(ext, FuncDef):
                s += self.visit(ext)
            else:
                s += self.visit(ext) + ';\n'
        return s

    def visit_Compound(self, n):
        s = self._make_indent() + '{\n'
        self.indent_level += 2
        if n.block_items:
            s += ''.join(self._generate_stmt(stmt) for stmt in n.block_items)
        self.indent_level -= 2
        s += self._make_indent() + '}\n'
        return s

    def visit_EmptyStatement(self, n):
        return ';'

    def visit_ParamList(self, n):
        return ', '.join(self.visit(param) for param in n.params)

    def visit_Return(self, n):
        s = 'return'
        if n.expr: s += ' ' + self.visit(n.expr)
        return s + ';'

    def visit_Break(self, n):
        return 'break;'

    def visit_Continue(self, n):
        return 'continue;'

    def visit_TernaryOp(self, n):
        s = self.visit(n.cond) + ' ? '
        s += self.visit(n.iftrue) + ' : '
        s += self.visit(n.iffalse)
        return s

    def visit_If(self, n):
        s = 'if ('
        if n.cond: s += self.visit(n.cond)
        s += ')\n'
        s += self._generate_stmt(n.iftrue, add_indent=True)
        if n.iffalse:
            s += self._make_indent() + 'else\n'
            s += self._generate_stmt(n.iffalse, add_indent=True)
        return s

    def visit_For(self, n):
        s = 'for ('
        if n.init: s += self.visit(n.init)
        s += ';'
        if n.cond: s += ' ' + self.visit(n.cond)
        s += ';'
        if n.next: s += ' ' + self.visit(n.next)
        s += ')\n'
        s += self._generate_stmt(n.stmt, add_indent=True)
        return s

    def visit_While(self, n):
        s = 'while ('
        if n.cond: s += self.visit(n.cond)
        s += ')\n'
        s += self._generate_stmt(n.stmt, add_indent=True)
        return s

    def visit_DoWhile(self, n):
        s = 'do\n'
        s += self._generate_stmt(n.stmt, add_indent=True)
        s += self._make_indent() + 'while ('
        if n.cond: s += self.visit(n.cond)
        s += ');'
        return s

    def visit_Switch(self, n):
        s = 'switch (' + self.visit(n.cond) + ')\n'
        s += self._generate_stmt(n.stmt, add_indent=True)
        return s

    def visit_Case(self, n):
        s = 'case ' + self.visit(n.expr) + ':\n'
        for stmt in n.stmts:
            s += self._generate_stmt(stmt, add_indent=True)
        return s

    def visit_Default(self, n):
        s = 'default:\n'
        for stmt in n.stmts:
            s += self._generate_stmt(stmt, add_indent=True)
        return s

    def visit_Label(self, n):
        return n.name + ':\n' + self._generate_stmt(n.stmt)

    def visit_Goto(self, n):
        return 'goto ' + n.name + ';'

    def visit_EllipsisParam(self, n):
        return '...'

    def visit_Struct(self, n):
        return self._generate_struct_union(n, 'struct')

    def visit_Typename(self, n):
        return self._generate_type(n.type)

    def visit_Union(self, n):
        return self._generate_struct_union(n, 'union')

    def visit_NamedInitializer(self, n):
        s = ''
        for name in n.name:
            if isinstance(name, ID):
                s += '.' + name.name
            elif isinstance(name, Constant):
                s += '[' + name.value + ']'
        s += ' = ' + self.visit(n.expr)
        return s

    def _generate_struct_union(self, n, name):
        """ Generates code for structs and unions. name should be either
            'struct' or union.
        """
        s = name + ' ' + (n.name or '')
        if n.decls:
            s += '\n'
            s += self._make_indent()
            self.indent_level += 2
            s += '{\n'
            for decl in n.decls:
                s += self._generate_stmt(decl)
            self.indent_level -= 2
            s += self._make_indent() + '}; \n'
        return s

    def _generate_stmt(self, n, add_indent=False):
        """ Generation from a statement node. This method exists as a wrapper
            for individual visit_* methods to handle different treatment of
            some statements in this context.
        """
        typ = type(n)
        if add_indent: self.indent_level += 2
        indent = self._make_indent()
        if add_indent: self.indent_level -= 2

        if typ in (
                Decl, Assignment, Cast, UnaryOp,
                BinaryOp, TernaryOp, FuncCall, ArrayRef,
                StructRef, Constant, ID, Typedef,
                ExprList):
            # These can also appear in an expression context so no semicolon
            # is added to them automatically
            #
            return indent + self.visit(n) + ';\n'            
        elif typ in (Compound,):
            # No extra indentation required before the opening brace of a
            # compound - because it consists of multiple lines it has to
            # compute its own indentation.
            #
            return self.visit(n)
        else:
            return indent + self.visit(n) + '\n'
            

    def _generate_decl(self, n):
        """ Generation from a Decl node.
        """
        s = ''
        if n.funcspec: s = ' '.join(n.funcspec) + ' '
        if n.storage: s += ' '.join(n.storage) + ' '
        s += self._generate_type(n.type)
        return s

    def _generate_type(self, n, modifiers=[]):
        """ Recursive generation from a type node. n is the type node.
            modifiers collects the PtrDecl, ArrayDecl and FuncDecl modifiers
            encountered on the way down to a TypeDecl, to allow proper
            generation from it.
        """
        typ = type(n)
        #~ print(n, modifiers)

        if typ == TypeDecl:
            s = ''
            if n.quals: s += ' '.join(n.quals) + ' '
            s += self.visit(n.type)

            nstr = n.declname if n.declname else ''
            # Resolve modifiers.
            # Wrap in parens to distinguish pointer to array and pointer to
            # function syntax.
            #
            for i, modifier in enumerate(modifiers):
                if isinstance(modifier, ArrayDecl):
                    if (i != 0 and isinstance(modifiers[i - 1], PtrDecl)):
                        nstr = '(' + nstr + ')'
                    nstr += '[' + self.visit(modifier.dim) + ']'
                elif isinstance(modifier, FuncDecl):
                    if (i != 0 and isinstance(modifiers[i - 1], PtrDecl)):
                        nstr = '(' + nstr + ')'
                    nstr += '(' + self.visit(modifier.args) + ')'
                elif isinstance(modifier, PtrDecl):
                    if modifier.quals:
                        nstr = '* %s %s' % (' '.join(modifier.quals), nstr)
                    else:
                        nstr = '*' + nstr
            if nstr: s += ' ' + nstr
            return s
        elif typ == Decl:
            return self._generate_decl(n.type)
        elif typ == Typename:
            return self._generate_type(n.type)
        elif typ == IdentifierType:
            return ' '.join(n.names) + ' '
        elif typ in (ArrayDecl, PtrDecl, FuncDecl):
            return self._generate_type(n.type, modifiers + [n])
        else:
            return self.visit(n)

    def _parenthesize_if(self, n, condition):
        """ Visits 'n' and returns its string representation, parenthesized
            if the condition function applied to the node returns True.
        """
        s = self.visit(n)
        if condition(n):
            return '(' + s + ')'
        else:
            return s

    def _parenthesize_unless_simple(self, n):
        """ Common use case for _parenthesize_if
        """
        return self._parenthesize_if(n, lambda d: not self._is_simple_node(d))

    def _is_simple_node(self, n):
        """ Returns True for nodes that are "simple" - i.e. nodes that always
            have higher precedence than operators.
        """
        return isinstance(n,(   Constant, ID, ArrayRef,
                                StructRef, FuncCall))



#class ParseC2Ast2C(pycparser.NodeVisitor):
class ParseC2Ast2C(object):
    """
    @summary: Class to parse C program to AST and then to C
    """
    def __init__(self):
        self.__inputfilename = ''
        self.ast = pycparser.c_ast
        self.ast_gen = pycparser.c_generator
        self.current_funct = ''          
        self.current_compund_func = pycparser.c_ast.Compound
        self.list_flow_program = [If,While,For,DoWhile,Switch,Case]
        self.flag_is_main = False
        self.actual_index_ast_node = 0
        self.nextLineNumEgual = []

        # For C file
        self.DONT_write_line_number = []        
        self.flag_assert = False
        self.flag_stdlib = False
        self.flag_stdio = False
        self.flag_stdint = False
        self.flag_others_h = False
        self.header_others = []


    def load2Parse(self, filename):
        """
        @summary: Load the C program and then to do the parse using pycparse
        @param filename: is the path of the C program file
        @return: NO
        """
        self.__inputfilename = filename
        # Load the input source file to build the AST, then generate the symbol table
        #
        path_cpp_args = os.path.join(os.path.dirname(__file__), "../utils/fake_libc_include")
        self.ast = pycparser.parse_file(self.__inputfilename, use_cpp=True, cpp_path=CPPPATH, cpp_args=r'-I'+path_cpp_args)        
        #~
        #self.ast.show()
        #sys.exit()
        
    
    @staticmethod
    def getNumberOfLine(nodeVar):
        #print(nodeVar)
        txt = str(nodeVar.coord)
        matchNumLine = re.search(r'(.[^:]+)$', txt)
        if matchNumLine:
            onlyNumber = matchNumLine.group(1).replace(":","")
            return int(onlyNumber)
            
            
    def readCFile(self, c_file):
        """
        Reading the source code to identify the includes that will not be write again. 
        For this we create a list to save the number of the lines identified.         
        """
        linesCFile = open(c_file)
        
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
        
        
    def expandFunction(self, stmt):
        
        if type(stmt) is Compound and type(stmt.block_items) is not type(None):
            index = 0            
            while index < len(stmt.block_items):
                self.nextLineNumEgual = []
                if (index+1) < len(stmt.block_items):
                    # Check k+1, i.e., check if in the line pointed by node there are
                    # more than one stement
                    #print(str(self.getNumberOfLine(stmt.block_items[index]))+" == "+str(self.getNumberOfLine(stmt.block_items[index+1])))                    
                    countTryNext = index
                    next_item = index
                    while self.getNumberOfLine(stmt.block_items[countTryNext]) == self.getNumberOfLine(stmt.block_items[next_item]):
                        #print(str(self.getNumberOfLine(stmt.block_items[countTryNext]))+" == "+str(self.getNumberOfLine(stmt.block_items[next_item])))
                        # save the nodes to print later
                        self.nextLineNumEgual.append(stmt.block_items[next_item])
                        #countTryNext += 1
                        next_item += 1
                
                self.getLine(stmt.block_items[index]) 
                
                if len(self.nextLineNumEgual) > 1:
                    index = next_item
                else:
                    index += 1
        else:
            self.getLine(stmt) 
                  
        
                
                
    def getLine(self, line):
        if self.checkFlowProgram(line):
            # Header of the flow program            
            #print("\t BF_Hflow: ",line.coord)  #DEBUG
            index = self.list_flow_program.index(type(line))
            get_flow_type = self.list_flow_program[index]
            generator_code = MyCGenerator()
            
            if get_flow_type == If:
                
                s = 'if ('
                if line.cond: s += generator_code.visit(line.cond)
                s += '){'
                print(s)
                self.expandFunction(line.iftrue)
                if line.iffalse:
                    print("assert(0); //by INCEPECTION")
                    print('}else{ ')
                    self.expandFunction(line.iffalse)
                    print("assert(0); //by INCEPECTION")
                    print("}")
                else:
                    print("assert(0); //by INCEPECTION")
                    print("}")
                
            elif get_flow_type == While:
                s = 'while ('
                if line.cond: s += generator_code.visit(line.cond)
                s += '){ '
                print(s)
                self.expandFunction(line.stmt)
                print("}")
                print("assert(0); //by INCEPECTION")
                
            elif get_flow_type == For:
                s = 'for ('
                if line.init: s += generator_code.visit(line.init)
                s += ';'
                if line.cond: s += ' ' + generator_code.visit(line.cond)
                s += ';'
                if line.next: s += ' ' + generator_code.visit(line.next)
                s += '){ '
                print(s)
                self.expandFunction(line.stmt)
                print("}")
                print("assert(0); //by INCEPECTION")
                
                
            elif get_flow_type == DoWhile:
                
                print('do {')
                self.expandFunction(line.stmt)
                s = '} while ('
                if line.cond: s += generator_code.visit(line.cond)
                s += ');'
                print(s)
                print("assert(0); //by INCEPECTION")
                
            elif get_flow_type == Switch:
                s = 'switch (' + generator_code.visit(line.cond) + ')\n{'
                print(s)
                self.expandFunction(line.stmt)
                print("}")
                
                
            elif get_flow_type == Case:
                s = 'case ' + generator_code.visit(line.expr) + ':\n'
                print(s)
                for stmt in line.stmts:
                    self.expandFunction(stmt)
            
            
        else:
            # >> Body of the flow program
            #print("\t\t BF_Bflow: ",line.coord) # DEBUG
            if type(line) == FuncCall:
                #print("-----------", line.name.name)
                if line.name.name in ['abort','exit']:
                    # Write leak assertion 
                    self.write_leak_assert(line)

            if len(self.nextLineNumEgual) > 1:
                tmp_k_1 = 0
                for node in self.nextLineNumEgual:
                    print(self.ast_gen.CGenerator()._generate_stmt(node).rstrip())

            else:
                print(self.ast_gen.CGenerator()._generate_stmt(line).rstrip())
                

    
    def checkFlowProgram(self, line):        
        if type(line) in self.list_flow_program:
            return True
        else:
            return False

    
    def checkIsTypeDefFromCode(self, astNode):
        """
        Identify the typedef node from AST related to C program, i.e.,
        exclude typedef from fake_libc_include/_fake_typedefs.h
        """
                
        if type(astNode) == Typedef:                
            matchTypeDef_Fake_typedefs = re.search(r'(fake_libc_include/_fake_typedefs.h)', str(astNode.coord))
            if not matchTypeDef_Fake_typedefs:
                #print(self.ast.ext[index].coord)
                return True
            else:
                return False
        
        
        
        
    def runAst(self):
        """
        Write the new instance of the analyzed C source code
        """
        # Check the includes and then write the nedded C headers to FORTES
        if not self.flag_assert:
            print("#include <assert.h> /** by INCEPCTION **/")

        if self.flag_others_h:
            for header in self.header_others:
                print(header.rstrip())
                
        print()               
                            
        
        # Write the code from the AST
        for index in range(0,len(self.ast.ext)): 
            
            # For use in other places
            self.actual_index_ast_node = index
                        
            # Print only the Typedef from C program, i.e., we exclude
            # fake_libc_include/_fake_typedefs.h
            if type(self.ast.ext[index]) == Typedef:
                if self.checkIsTypeDefFromCode(self.ast.ext[index]):
                    #print(self.ast.ext[index].coord)
                    print(self.ast_gen.CGenerator()._generate_stmt(self.ast.ext[index]))
                    
            if type(self.ast.ext[index]) is not Typedef:
                # For each Function identified we expand its compound
                
                if type(self.ast.ext[index]) == FuncDef:
                    self.flag_is_main = False
                    # >> Header of the function
                    #print(self.ast.ext[index].coord)  # DEBUG
                    print(self.ast_gen.CGenerator().visit(self.ast.ext[index].decl))
                    print("{")

                    # >> Body of the function
                    if type(self.ast.ext[index].body) is Compound:                                                
                        self.expandFunction(self.ast.ext[index].body)

                    print("}\n")

        # >> END OF THE PROGRAM


# -------------------------------------------------
# Main python program
# -------------------------------------------------

if __name__ == "__main__":  

    path_input_c_file = sys.argv[1]
    runWrite = ParseC2Ast2C()
    runWrite.load2Parse(path_input_c_file)
    runWrite.readCFile(path_input_c_file)

    runWrite.runAst()