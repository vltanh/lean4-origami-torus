#!/usr/bin/env python3
"""Small incremental Boolean producer using Z3's finite-domain SAT backend.

This is a discovery tool, not a trusted proof checker. Exported UNSAT
claims must still be replayed by the independent CNF/RUP checkers.
The interface matches the existing research SAT adapter; close() also
allows callers to release native contexts between independent cells.
"""

import ctypes as ct
from ctypes.util import find_library


class FastSAT:
    def __init__(self, variables, clauses):
        self.z = z = ct.CDLL(find_library('z3'))
        pointer, unsigned = ct.c_void_p, ct.c_uint
        self.P = pointer
        declarations = (
            ('Z3_mk_config', pointer, []),
            ('Z3_mk_context', pointer, [pointer]),
            ('Z3_del_config', None, [pointer]),
            ('Z3_del_context', None, [pointer]),
            ('Z3_mk_string_symbol', pointer, [pointer, ct.c_char_p]),
            ('Z3_mk_solver_for_logic', pointer, [pointer, pointer]),
            ('Z3_solver_inc_ref', None, [pointer, pointer]),
            ('Z3_mk_bool_sort', pointer, [pointer]),
            ('Z3_mk_int_symbol', pointer, [pointer, ct.c_int]),
            ('Z3_mk_const', pointer, [pointer, pointer, pointer]),
            ('Z3_mk_not', pointer, [pointer, pointer]),
            ('Z3_mk_or', pointer, [pointer, unsigned, ct.POINTER(pointer)]),
            ('Z3_solver_assert', None, [pointer, pointer, pointer]),
            ('Z3_solver_check', ct.c_int, [pointer, pointer]),
            ('Z3_solver_push', None, [pointer, pointer]),
            ('Z3_solver_pop', None, [pointer, pointer, unsigned]),
            ('Z3_solver_get_model', pointer, [pointer, pointer]),
            ('Z3_model_inc_ref', None, [pointer, pointer]),
            ('Z3_model_dec_ref', None, [pointer, pointer]),
            ('Z3_model_eval', ct.c_bool, [pointer, pointer, pointer, ct.c_bool, ct.POINTER(pointer)]),
            ('Z3_get_bool_value', ct.c_int, [pointer, pointer]),
        )
        for name, result, arguments in declarations:
            function = getattr(z, name)
            function.restype, function.argtypes = result, arguments
        config = z.Z3_mk_config()
        self.ctx = z.Z3_mk_context(config)
        z.Z3_del_config(config)
        logic = z.Z3_mk_string_symbol(self.ctx, b'QF_FD')
        self.s = z.Z3_mk_solver_for_logic(self.ctx, logic)
        assert self.s
        z.Z3_solver_inc_ref(self.ctx, self.s)
        sort = z.Z3_mk_bool_sort(self.ctx)
        self.v = {i: z.Z3_mk_const(self.ctx, z.Z3_mk_int_symbol(self.ctx, i), sort)
                  for i in range(1, variables+1)}
        self.v.update({-i: z.Z3_mk_not(self.ctx, atom) for i, atom in list(self.v.items())})
        for clause in clauses:
            self.add(clause)

    def add(self, clause):
        assert self.ctx
        literals = (self.P*len(clause))(*(self.v[value] for value in clause))
        expression = self.z.Z3_mk_or(self.ctx, len(clause), literals)
        self.z.Z3_solver_assert(self.ctx, self.s, expression)

    def check(self):
        assert self.ctx
        return self.z.Z3_solver_check(self.ctx, self.s)

    def model(self, count=70):
        assert self.ctx
        z, context = self.z, self.ctx
        model = z.Z3_solver_get_model(context, self.s)
        assert model
        z.Z3_model_inc_ref(context, model)
        result = []
        try:
            for i in range(1, count+1):
                value = self.P()
                assert z.Z3_model_eval(context, model, self.v[i], True, ct.byref(value))
                truth = z.Z3_get_bool_value(context, value.value)
                assert truth in (-1, 1)
                result.append(truth)
        finally:
            z.Z3_model_dec_ref(context, model)
        return result

    def push(self):
        assert self.ctx
        self.z.Z3_solver_push(self.ctx, self.s)

    def pop(self):
        assert self.ctx
        self.z.Z3_solver_pop(self.ctx, self.s, 1)

    def close(self):
        if self.ctx:
            self.z.Z3_del_context(self.ctx)
            self.ctx = None

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
