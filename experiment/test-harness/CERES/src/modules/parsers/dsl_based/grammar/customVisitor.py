import re

from build.dsl_grammarParser import dsl_grammarParser
from build.dsl_grammarVisitor import dsl_grammarVisitor
from helpers import *

filename = None
file = None


class customVisitor(dsl_grammarVisitor):
    def __init__(self, output_path):
        global filename
        filename = output_path

    def visitNw(self, ctx: dsl_grammarParser.NwContext):
        val = '\n'
        return val

    def visitStructstmnt(self, ctx: dsl_grammarParser.StructstmntContext):
        global file

        lhs = self.visitNterm(ctx.getChild(0)).name
        params = self.visitNterm(ctx.getChild(0)).params
        if params == None:
            file.write('\ndef {}(Begin):\n    Temp = Begin\n'.format(lhs))
        else:
            params1 = params[:-1] + ', Begin)'
            file.write('\ndef {}{}:\n    Temp = Begin\n'.format(lhs, params1))
        sp = '    '
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('StructrhsContext'):
                option = self.visitStructrhs(ctx.getChild(i))
                if len(option) == 1:
                    b = 0
                    fields = option[0].fields
                    assignments = option[0].assignment
                    condition = option[0].condition
                    precondition_ent = option[0].precondition_ent
                    precondition = option[0].precondition
                    if precondition != None:
                        file.write(
                            1 * sp + 'if not ({}):\n{}return True, 0, None, Begin\n'.format(precondition, 2 * sp))
                    if precondition_ent != None:
                        b = 1
                        file.write(
                            1 * sp + 'if ({}):\n'.format(precondition_ent))
                    for i in range(0, len(fields)):
                        if fields[i].type == 'Nterm':
                            if fields[i].params == None:
                                file.write((i + 1 + b) * sp + 'FLAG_{}, SIZE_{}, VAL_{}, Begin = {}(Begin)\n'.format(
                                    fields[i].name,
                                    fields[i].name,
                                    fields[i].name,
                                    fields[i].name))
                                if fields[i].opt == False:
                                    file.write((i + 1 + b) * sp + 'if FLAG_{}:\n'.format(fields[i].name))
                                else:
                                    file.write((i + 1 + b) * sp + 'if True:\n'.format(fields[i].name))
                            else:
                                params1 = fields[i].params[:-1] + ', Begin)'
                                file.write(
                                    (i + 1 + b) * sp + 'FLAG_{}, SIZE_{}, VAL_{}, Begin = {}{}\n'.format(fields[i].name,
                                                                                                         fields[i].name,
                                                                                                         fields[i].name,
                                                                                                         fields[i].name,
                                                                                                         params1))
                                if fields[i].opt == False:
                                    file.write((i + 1 + b) * sp + 'if FLAG_{}:\n'.format(fields[i].name))
                                else:
                                    file.write((i + 1 + b) * sp + 'if True:\n'.format(fields[i].name))
                        elif fields[i].type == 'Term':
                            file.write(
                                (
                                        i + 1 + b) * sp + 'FLAG_{}, SIZE_{}, VAL_{}, Begin = match(\'{}\', True, Begin)\n'.format(
                                    fields[i].name,
                                    fields[i].name,
                                    fields[i].name,
                                    fields[
                                        i].name))
                            file.write((i + 1 + b) * sp + 'if FLAG_{}:\n'.format(fields[i].name))
                    for j in range(0, len(assignments)):
                        file.write((i + 2 + b) * sp + '{}\n'.format(assignments[j]))
                    if condition != None:
                        file.write((i + 2 + b) * sp + 'if not ({}):\n{}return False, 0, None, Temp\n'.format(condition,
                                                                                                             (
                                                                                                                     i + 3 + b) * sp))
                    file.write((i + 2 + b) * sp + 'return True, SIZE_{}, VAL_{}, Begin'
                                                  '\n'.format(lhs, lhs))
                elif len(option) > 1:
                    for k in range(0, len(option)):
                        b = 0
                        fields = option[k].fields
                        assignments = option[k].assignment
                        condition = option[k].condition
                        precondition = option[k].precondition
                        precondition_ent = option[k].precondition_ent
                        if precondition != None:
                            file.write(
                                1 * sp + 'if not ({}):\n{}return True, 0, None, Begin\n'.format(precondition, 2 * sp))
                        if precondition_ent != None:
                            b = 1
                            file.write(
                                1 * sp + 'if ({}):\n'.format(precondition_ent))
                        for i in range(0, len(fields)):
                            if fields[i].type == 'Nterm':
                                if fields[i].params == None:
                                    file.write(
                                        (i + 1 + b) * sp + 'FLAG_{}, SIZE_{}, VAL_{}, Begin = {}()\n'.format(
                                            fields[i].name,
                                            fields[i].name,
                                            fields[i].name,
                                            fields[
                                                i].name))
                                    if fields[i].opt == False:
                                        file.write((i + 1 + b) * sp + 'if FLAG_{}:\n'.format(fields[i].name))
                                    else:
                                        file.write((i + 1 + b) * sp + 'if True:\n'.format(fields[i].name))
                                else:
                                    params1 = fields[i].params[:-1] + ', Begin)'
                                    file.write(
                                        (i + 1 + b) * sp + 'FLAG_{}, SIZE_{}, VAL_{}, Begin = {}{}\n'.format(
                                            fields[i].name,
                                            fields[i].name,
                                            fields[i].name,
                                            fields[i].name,
                                            params1))
                                    if fields[i].opt == False:
                                        file.write((i + 1 + b) * sp + 'if FLAG_{}:\n'.format(fields[i].name))
                                    else:
                                        file.write((i + 1 + b) * sp + 'if True:\n'.format(fields[i].name))
                            elif fields[i].type == 'Term':
                                file.write((
                                                   i + 1) * sp + 'FLAG_{}, SIZE_{}, VAL_{}, Begin = match(\'{}\', True, Begin)\n'.format(
                                    fields[i].name,
                                    fields[i].name,
                                    fields[i].name,
                                    fields[
                                        i].name))
                                file.write((i + 1 + b) * sp + 'if FLAG_{}:\n'.format(fields[i].name))
                        for j in range(0, len(assignments)):
                            file.write((i + 2 + b) * sp + '{}\n'.format(assignments[j]))
                        if condition != None:
                            file.write(
                                (i + 2 + b) * sp + 'if not ({}):\n{}return False, 0, None, Temp\n'.format(condition,
                                                                                                          (
                                                                                                                  i + 3 + b) * sp))
                        file.write((i + 2 + b) * sp + 'return True, SIZE_{}, VAL_{}, Begin\n'.format(lhs, lhs))
            elif str(type(ctx.getChild(i))).__contains__('StructrhsnotermContext'):
                option = self.visitStructrhsnoterm(ctx.getChild(i))
                if len(option) == 1:
                    b = 0
                    fields = option[0].fields
                    assignments = option[0].assignment
                    condition = option[0].condition
                    precondition = option[0].precondition
                    precondition_ent = option[0].precondition_ent
                    if precondition != None:
                        file.write(
                            1 * sp + 'if not ({}):\n{}return True, 0, None, Begin\n'.format(precondition, 2 * sp))
                    if precondition_ent != None:
                        b = 1
                        file.write(
                            1 * sp + 'if ({}):\n'.format(precondition_ent))
                    for i in range(0, len(fields)):
                        if fields[i].type == 'Noterm':
                            file.write(
                                (
                                        i + 1 + b) * sp + 'FLAG_not_{}, SIZE_{}, VAL_{}, Begin = match(\'{}\', False, Begin)\n'.format(
                                    fields[i].name,
                                    fields[i].name,
                                    fields[i].name,
                                    fields[i].name))
                            file.write((i + 1 + b) * sp + 'if FLAG_not_{}:\n'.format(fields[i].name))
                    for j in range(0, len(assignments)):
                        file.write((i + 2 + b) * sp + '{}\n'.format(assignments[j]))
                    if condition != None:
                        file.write((i + 2 + b) * sp + 'if not ({}):\n{}return False, 0, None, Temp\n'.format(condition,
                                                                                                             (
                                                                                                                     i + 3 + b) * sp))
                    file.write((i + 2 + b) * sp + 'return True, SIZE_{}, VAL_{}, Begin\n'.format(lhs, lhs))
                elif len(option) > 1:
                    for k in range(0, len(option)):
                        b = 0
                        fields = option[k].fields
                        assignments = option[k].assignment
                        condition = option[k].condition
                        precondition = option[k].precondition
                        precondition_ent = option[k].precondition_ent
                        if precondition != None:
                            file.write(
                                1 * sp + 'if not ({}):\n{}return True, 0, None, Begin\n'.format(precondition, 2 * sp))
                        if precondition_ent != None:
                            b = 1
                            file.write(
                                1 * sp + 'if ({}):\n'.format(precondition_ent))
                        for i in range(0, len(fields)):
                            if fields[i].type == 'Noterm':
                                file.write(
                                    (
                                            i + 1 + b) * sp + 'FLAG_not_{}, SIZE_{}, VAL_{}, Begin = match(\'{}\', False, Begin)\n'.format(
                                        fields[i].name,
                                        fields[i].name,
                                        fields[i].name,
                                        fields[i].name))
                                file.write((i + 1 + b) * sp + 'if FLAG_not_{}:\n'.format(fields[i].name))
                        for j in range(0, len(assignments)):
                            file.write((i + 2 + b) * sp + '{}\n'.format(assignments[j]))
                        if condition != None:
                            file.write(
                                (i + 2 + b) * sp + 'if not ({}):\n{}return False, 0, None, Temp\n'.format(condition,
                                                                                                          (
                                                                                                                  i + 3 + b) * sp))
                        file.write((i + 2 + b) * sp + 'return True, SIZE_{}, VAL_{}, Begin\n'.format(lhs, lhs))
        file.write(1 * sp + 'return False, 0, None, Temp\n')
        return super().visitStructstmnt(ctx)

    def visitNterm(self, ctx: dsl_grammarParser.NtermContext):
        val = str(ctx.getChild(0))
        params = None
        if ctx.getChild(1) != None:
            params = self.visitParams(ctx.getChild(1), True)
        fld = Field('Nterm', val, params)
        return fld

    def visitLetter(self, ctx: dsl_grammarParser.LetterContext):
        val = str(ctx.getChild(0))
        return val

    def visitNumber(self, ctx: dsl_grammarParser.NumberContext):
        val = str(ctx.getChild(0))
        return val

    def visitTerm(self, ctx: dsl_grammarParser.TermContext):
        val = None
        params = None
        if str(type(ctx.getChild(0))).__contains__('LetterContext'):
            val = self.visitLetter(ctx.getChild(0))
        elif str(type(ctx.getChild(0))).__contains__('NumberContext'):
            val = self.visitNumber(ctx.getChild(0))
        elif str(type(ctx.getChild(0))).__contains__('LetterContext'):
            val = self.visitLetter(ctx.getChild(0))
        fld = Field('Term', val, params)
        return fld

    def visitAttrname(self, ctx: dsl_grammarParser.AttrnameContext):
        val = str(ctx.getChild(0))
        return val

    def visitUs(self, ctx: dsl_grammarParser.UsContext):
        val = str(ctx.getChild(0))
        return val

    def visitGt(self, ctx: dsl_grammarParser.GtContext):
        val = ' > '
        return val

    def visitLt(self, ctx: dsl_grammarParser.LtContext):
        val = ' < '
        return val

    def visitGte(self, ctx: dsl_grammarParser.GteContext):
        val = ' >= '
        return val

    def visitLte(self, ctx: dsl_grammarParser.LteContext):
        val = ' <= '
        return val

    def visitEq(self, ctx: dsl_grammarParser.EqContext):
        val = ' == '
        return val

    def visitNeq(self, ctx: dsl_grammarParser.NeqContext):
        val = ' != '
        return val

    def visitAndg(self, ctx: dsl_grammarParser.AndgContext):
        val = ' and '
        return val

    def visitOrg(self, ctx: dsl_grammarParser.OrgContext):
        val = ' or '
        return val

    def visitNotg(self, ctx: dsl_grammarParser.NotgContext):
        val = ' !'
        return val

    def visitAssgnop(self, ctx: dsl_grammarParser.AssgnopContext):
        val = ' = '
        return val

    def visitAdd(self, ctx: dsl_grammarParser.AddContext):
        val = ' + '
        return val

    def visitMinus(self, ctx: dsl_grammarParser.MinusContext):
        val = ' - '
        return val

    def visitMul(self, ctx: dsl_grammarParser.MulContext):
        val = ' * '
        return val

    def visitDiv(self, ctx: dsl_grammarParser.DivContext):
        val = ' / '
        return val

    def visitAttrbt(self, ctx: dsl_grammarParser.AttrbtContext):
        val = self.visitAttrname(ctx.getChild(0)) + self.visitUs(ctx.getChild(1)) + str(
            self.visitNterm(ctx.getChild(2)).name)
        return val

    def visitArrexpr(self, ctx: dsl_grammarParser.ArrexprContext):
        code = ''
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('ArrexprContext'):
                code = code + self.visitArrexpr(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('ArrtermContext'):
                code = code + self.visitArrterm(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('AddContext'):
                code = code + self.visitAdd(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('MinusContext'):
                code = code + self.visitMinus(ctx.getChild(i))

        return code

    def visitCondblock(self, ctx: dsl_grammarParser.CondblockContext):
        code = self.visitBoolgexpr(ctx.getChild(2))
        return code

    def visitPrecondition_ent(self, ctx: dsl_grammarParser.Precondition_entContext):
        code = self.visitBoolgexpr(ctx.getChild(2))
        return code

    def visitPrecondition(self, ctx: dsl_grammarParser.PreconditionContext):
        code = self.visitBoolgexpr(ctx.getChild(2))
        return code

    def visitArrterm(self, ctx: dsl_grammarParser.ArrtermContext):
        code = ''
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('ArrfactorgContext'):
                code = code + self.visitArrfactorg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('ArrtermContext'):
                code = code + self.visitArrterm(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('MulContext'):
                code = code + self.visitMul(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('DivContext'):
                code = code + self.visitDiv(ctx.getChild(i))

        return code

    def visitArrfactorg(self, ctx: dsl_grammarParser.ArrfactorgContext):
        code = ''
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('AttrbtContext'):
                code = code + self.visitAttrbt(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('NumberContext'):
                code = code + self.visitNumber(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('LfbContext'):
                code = code + self.visitLfb(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('RfbContext'):
                code = code + self.visitRfb(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('ArrexprContext'):
                code = code + self.visitArrexpr(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('MinusContext'):
                code = code + self.visitMinus(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('ArrfactorgContext'):
                code = code + self.visitArrfactorg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('IndexContext'):
                code = code + self.visitIndex(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('ExtfunccallContext'):
                code = code + self.visitExtfunccall(ctx.getChild(i))

        return code

    def visitLfb(self, ctx: dsl_grammarParser.LfbContext):
        val = ' ( '
        return val

    def visitAssignstmnt(self, ctx: dsl_grammarParser.AssignstmntContext):
        code = ''
        code = code + self.visitAttrbt(ctx.getChild(0))
        code = code + self.visitAssgnop(ctx.getChild(1))
        if str(type(ctx.getChild(2))).__contains__('ArrexprContext'):
            code = code + self.visitArrexpr(ctx.getChild(2))
        elif str(type(ctx.getChild(2))).__contains__('BoolgexprContext'):
            code = code + self.visitBoolgexpr(ctx.getChild(2))
        elif str(type(ctx.getChild(2))).__contains__('NullgContext'):
            code = code + self.visitNullg(ctx.getChild(2))
        elif str(type(ctx.getChild(2))).__contains__('RetupleContext'):
            code = code + self.visitRetuple(ctx.getChild(2))
        elif str(type(ctx.getChild(2))).__contains__('RelistContext'):
            code = code + self.visitRelist(ctx.getChild(2))
        return code

    def visitRfb(self, ctx: dsl_grammarParser.RfbContext):
        val = ' ) '
        return val

    def visitBoolgexpr(self, ctx: dsl_grammarParser.BoolgexprContext):
        code = ''
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('BoolgexprContext'):
                code = code + self.visitBoolgexpr(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('BoolgfactorgContext'):
                code = code + self.visitBoolgfactorg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('AndgContext'):
                code = code + self.visitAndg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('OrgContext'):
                code = code + self.visitOrg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('EqContext'):
                code = code + self.visitEq(ctx.getChild(i))
        return code

    def visitBoolgfactorg(self, ctx: dsl_grammarParser.BoolgfactorgContext):
        code = ''
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('AttrbtContext'):
                code = code + self.visitAttrbt(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('BoolgContext'):
                code = code + self.visitBoolg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('LfbContext'):
                code = code + self.visitLfb(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('RfbContext'):
                code = code + self.visitRfb(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('BoolgexprContext'):
                code = code + self.visitBoolgexpr(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('NotgContext'):
                code = code + self.visitNotg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('BoolgfactorgContext'):
                code = code + self.visitBoolgfactorg(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('BoolrelationContext'):
                code = code + self.visitBoolrelation(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('IndexContext'):
                code = code + self.visitIndex(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('ExtfunccallContext'):
                code = code + self.visitExtfunccall(ctx.getChild(i))
        return code

    def visitBoolrelation(self, ctx: dsl_grammarParser.BoolrelationContext):
        code = ''
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('ArrexprContext'):
                code = code + self.visitArrexpr(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('LtContext'):
                code = code + self.visitLt(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('LteContext'):
                code = code + self.visitLte(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('GtContext'):
                code = code + self.visitGt(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('GteContext'):
                code = code + self.visitGte(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('EqContext'):
                code = code + self.visitEq(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('NeqContext'):
                code = code + self.visitNeq(ctx.getChild(i))
        return code

    def visitAssignstmntblock(self, ctx: dsl_grammarParser.AssignstmntblockContext):
        code = []
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('AssignstmntContext'):
                code.append(self.visitAssignstmnt(ctx.getChild(i)))
        return code

    def visitNoterm(self, ctx: dsl_grammarParser.NotermContext):
        val = self.visitTerm(ctx.getChild(1))
        params = None
        fld = Field('Noterm', val.name, params)
        return fld

    def visitStart(self, ctx: dsl_grammarParser.StartContext):
        global file, filename
        file = open(filename, "w+")
        file.write(
            'import sys\nsys.setrecursionlimit(5000)\n\nfrom modules.helper import *\nfrom modules.x509_ds import *\n\n')

        super().visitStart(ctx)
        file.close()
        return

    def visitParams(self, ctx: dsl_grammarParser.ParamsContext, from_nterm):
        if from_nterm:
            params = '('
        else:
            params = '(['
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('ArrexprContext'):
                params = params + self.visitArrexpr(ctx.getChild(i)) + ', '
            elif str(type(ctx.getChild(i))).__contains__('BoolgexprContext'):
                params = params + self.visitBoolgexpr(ctx.getChild(i)) + ', '
        if from_nterm:
            params = params[:-2] + ')'
        else:
            params = params[:-2] + '])'
        return params

    def visitRetuple(self, ctx: dsl_grammarParser.ParamsContext):
        params = '('
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('AttrbtContext'):
                params = params + self.visitAttrbt(ctx.getChild(i)) + ', '
        params = params[:-2] + ')'
        return params

    def visitRelist(self, ctx: dsl_grammarParser.ParamsContext):
        params = '['
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('AttrbtContext'):
                params = params + self.visitAttrbt(ctx.getChild(i)) + ', '
        params = params[:-2] + ']'
        return params

    def visitStructrhs1(self, ctx: dsl_grammarParser.Structrhs1Context):
        fields = []
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('NtermContext'):
                opt = False
                if i + 2 < ctx.getChildCount() and str(ctx.getChild(i + 2)) == '?':
                    opt = True
                nterm = self.visitNterm(ctx.getChild(i))
                nterm.opt = opt
                fields.append(nterm)
            elif str(type(ctx.getChild(i))).__contains__('TermContext'):
                term = self.visitTerm(ctx.getChild(i))
                fields.append(term)
        return fields

    def visitStructrhs2(self, ctx: dsl_grammarParser.Structrhs2Context):
        fieldsOpt = []
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('NtermContext'):
                nterm = self.visitNterm(ctx.getChild(i))
                fieldsOpt.append(nterm)
            elif str(type(ctx.getChild(i))).__contains__('TermContext'):
                term = self.visitTerm(ctx.getChild(i))
                fieldsOpt.append(term)
        return fieldsOpt

    def visitStructrhs3(self, ctx: dsl_grammarParser.Structrhs3Context):
        fieldsOpt = []
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('NotermContext'):
                noterm = self.visitNoterm(ctx.getChild(i))
                fieldsOpt.append(noterm)
        return fieldsOpt

    def visitStructrhscodes(self, ctx: dsl_grammarParser.StructrhscodesContext):
        assignments = None
        condition = None
        precondition = None
        precondition_ent = None
        for i in range(0, ctx.getChildCount()):
            if str(type(ctx.getChild(i))).__contains__('AssignstmntblockContext'):
                assignments = self.visitAssignstmntblock(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('CondblockContext'):
                condition = self.visitCondblock(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('PreconditionContext'):
                precondition = self.visitPrecondition(ctx.getChild(i))
            elif str(type(ctx.getChild(i))).__contains__('Precondition_entContext'):
                precondition_ent = self.visitPrecondition_ent(ctx.getChild(i))
        return Asscond(assignments, precondition, precondition_ent, condition)

    def visitStructrhs(self, ctx: dsl_grammarParser.StructrhsContext):
        ret = []
        if str(type(ctx.getChild(0))).__contains__('Structrhs1Context'):
            fields = self.visitStructrhs1(ctx.getChild(0))
            code = self.visitStructrhscodes(ctx.getChild(2))
            code2 = []
            for k in code.assignment:
                match = re.findall(r'\$\d+\$', k)
                if match != None:
                    for p in match:
                        index = int(p[1:len(p) - 1]) - 1
                        if fields[index].type == 'Term':
                            k = k.replace(p, '\'{}\''.format(str(fields[index].name)))
                        elif fields[index].type == 'Nterm':
                            k = k.replace(p, 'VAL_' + str(fields[index].name))
                    code2.append(k)
                else:
                    code2.append(k)
            ret.append(Rhsrule(fields, code2, code.precondition, code.precondition_ent, code.condition))
        elif str(type(ctx.getChild(0))).__contains__('Structrhs2Context'):
            fields = self.visitStructrhs1(ctx.getChild(0))
            code = self.visitStructrhscodes(ctx.getChild(2))
            for p in fields:
                code2 = []
                for k in code.assignment:
                    match = re.search(r'\$1\$', k)
                    if match != None:
                        if p.type == 'Term':
                            k = re.sub(r'\$1\$', '\'{}\''.format(str(p.name)), k)
                            code2.append(k)
                        elif p.type == 'Nterm':
                            k = re.sub(r'\$1\$', 'VAL_' + str(p.name), k)
                            code2.append(k)
                    else:
                        code2.append(k)
                ret.append(Rhsrule([p], code2, code.precondition, code.precondition_ent, code.condition))
        elif str(type(ctx.getChild(0))).__contains__('RangegContext'):
            fields = self.visitRangeg(ctx.getChild(0))
            code = self.visitStructrhscodes(ctx.getChild(2))
            for p in fields:
                code2 = []
                for k in code.assignment:
                    match = re.search(r'\$1\$', k)
                    if match != None:
                        k = re.sub(r'\$1\$', '\'{}\''.format(str(p.name)), k)
                        code2.append(k)
                    else:
                        code2.append(k)
                ret.append(Rhsrule([p], code2, code.precondition, code.precondition_ent, code.condition))

        return ret

    def visitStructrhsnoterm(self, ctx: dsl_grammarParser.StructrhsnotermContext):
        ret = []
        if str(type(ctx.getChild(0))).__contains__('Structrhs3Context'):
            fields = self.visitStructrhs3(ctx.getChild(0))
            code = self.visitStructrhscodes(ctx.getChild(2))
            ret.append(Rhsrule(fields, code.assignment, code.precondition, code.precondition_ent, code.condition))

        return ret

    def visitExtfunc(self, ctx: dsl_grammarParser.ExtfuncContext):
        x = str(ctx.getChild(0))[5:]
        return x

    def visitExtfunccall(self, ctx: dsl_grammarParser.ExtfunccallContext):
        return str(self.visitExtfunc(ctx.getChild(0))) + str(self.visitParams(ctx.getChild(1), False))

    def visitRangeg(self, ctx: dsl_grammarParser.RangegContext):
        fields = []
        if str(type(ctx.getChild(2))).__contains__('NumberContext'):
            min = int(self.visitNumber(ctx.getChild(2)))
            max = int(self.visitNumber(ctx.getChild(4)))
            if min < max:
                for i in range(min, max + 1):
                    val = i
                    params = None
                    fld = Field('Term', val, params)
                    fields.append(fld)
            else:
                for i in range(max, min + 1):
                    val = i
                    params = None
                    fld = Field('Term', val, params)
                    fields.append(fld)
        elif str(type(ctx.getChild(2))).__contains__('LetterContext'):
            min = ord(self.visitLetter(ctx.getChild(2)))
            max = ord(self.visitLetter(ctx.getChild(4)))
            if min < max:
                for i in range(min, max + 1):
                    val = chr(i)
                    params = None
                    fld = Field('Term', val, params)
                    fields.append(fld)
            else:
                for i in range(max, min + 1):
                    val = chr(i)
                    params = None
                    fld = Field('Term', val, params)
                    fields.append(fld)

        return fields

    def visitIndex(self, ctx: dsl_grammarParser.IndexContext):
        val = str(ctx.getChild(0)) + self.visitNumber(ctx.getChild(1)) + str(ctx.getChild(2))
        return val

    def visitNullg(self, ctx: dsl_grammarParser.NullgContext):
        val = ' None '
        return val
