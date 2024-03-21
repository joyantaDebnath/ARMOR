import sys

sys.setrecursionlimit(7000)


class Rhsrule:
    def __init__(self, fields, assignment, precondition, precondition_ent, condition):
        self.fields = fields
        self.assignment = assignment
        self.precondition = precondition
        self.precondition_ent = precondition_ent
        self.condition = condition


class Asscond:
    def __init__(self, assignment, precondition, precondition_ent, condition):
        self.assignment = assignment
        self.precondition = precondition
        self.precondition_ent = precondition_ent
        self.condition = condition


class Field:
    def __init__(self, type, name, params):
        self.type = type
        self.name = name
        self.params = params
        self.opt = False
