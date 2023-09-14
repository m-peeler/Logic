# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from re import I
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdecimal())

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    # return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}

@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        output = ""
        # Task 1.1
        if is_variable(self.root) or is_constant(self.root):
            # Only includes central node value because there are no child nodes
            output = self.root
        elif is_unary(self.root):
            # Outputs unary operator at node followed by single argument to the unary operator
            # Prorder traversal (Node -> Child)
            output = str(self.root) + str(self.first)
        else:
            # Outputs first argument, operator, second argument
            # In-Order traversal (Left Child -> Node -> Right Child)
            output = '(' + str(self.first) + str(self.root) + str(self.second) + ')'
        return output
        


    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2
        vars = set()
        if is_variable(self.root):
            # Adds root if it is a variable
            vars.add(self.root)
        elif is_unary(self.root):
            # Returns the set of variables present in the first child node
            # if operator is Unary
            vars = self.first.variables()
        elif is_binary(self.root):
            # Returns the union of variables present in the two children nodes
            # if operator is binary
            vars = self.first.variables().union(self.second.variables())
        return vars

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        ops = set()
        if is_constant(self.root):
            # Adds the current operator (any T or F)
            ops.add(self.root)
        elif is_unary(self.root):
            # Adds the current unary operator and any operators present in the child
            ops.add(self.root)
            ops = ops.union(self.first.operators())
        elif is_binary(self.root):
            # Adds the current binary operator any any operators present in either child
            ops.add(self.root)
            ops = ops.union(self.first.operators().union(self.second.operators()))
        return  ops

        #### MICHAEL'S NOTES ####
        # Tasks 1.1 - 1.3 are all relatively easy and straightforward, but for the very 
        # poor error messages when asserts fail, as they don't show the incorrect answers and
        # do not clarify what the issue is.
        
    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        if string == "":
            return None, ""

        elif string[0] == "(":
            first, remains_fst = Formula._parse_prefix(string[1:])
            op, remains_snd = "", ""
            if remains_fst[0] in ['&', '|']:
                op, remains_snd = remains_fst[0], remains_fst[1:]
            elif remains_fst[0:2] == '->':
                op, remains_snd = remains_fst[0:2], remains_fst[2:]
            second, remains_trd = Formula._parse_prefix(remains_snd)

            fail = False
            if first is None or second is None:
                fail = True
            elif op not in ["&", "|", "->"]:
                fail = True
            elif remains_trd == "" or remains_trd[0] != ")":
                fail = True

            if fail:
                return None, "Unexpected symbol"            
            else:
                return Formula(op, first, second), remains_trd[1:]

        elif string[0] == "~":
            var, remains = Formula._parse_prefix(string[1:])
            if var is None:
                return None, "Unexpected symbol"
            return Formula("~", var), remains

        elif string[0] in ["T","F"]:
            return Formula(string[0]), string[1:]

        elif string[0] >= 'p' and string[0] <= 'z':
            ind = 1
            while ind < len(string) and string[ind].isdigit():
                ind += 1
            return Formula(string[0:ind]), string[ind:]

        else:
            return None, "Unexpected symbol"

        #### MICHAEL'S NOTES ####
        # This task, solved to the best of my ability, is a massive leap up in difficulty
        # from everything else we have done in the book, and will go on to do, as far as I
        # have sofar done. This is not aided by the book's relatively poor and unintuitive description
        # of how exactly this function is intended to work. Basically, it should be able to fully, 
        # recursively parse a Formula if the string is valid, or get the longest possible valid 
        # Formula that "prefixes" the string. This should be done by addressing a single token at a time,
        # typically by simply returning the token as a Formula, except in the case of the unary operator 
        # '~' or the binary operator, which you discover when you reach the '(' token. These should use 
        # recursion to identify the first parameter, the operator, and the second parameter, and should then
        # discover the binary operator ending token ')' at the start of the remaining string. I had to
        # sit thinking for a significant length of time and continually rereading the problem for a while
        # before I grasped the extent of the problem, which was not necessarily helped by the scant number of
        # examples.

        



        

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        form, rem = Formula._parse_prefix(string) 
        return form is not None and rem == ""
        
    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6
        form, rem = Formula._parse_prefix(string)
        return form

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7
        if is_variable(self.root) or is_constant(self.root):
            return str(self.root)
        elif is_unary(self.root):
            return str(self.root) + self.first.polish()
        elif is_binary(self.root):
            return str(self.root) + self.first.polish() + self.second.polish()
        else:
            return None
            

    @staticmethod
    def _parse_polish(string: str) -> Tuple[Union[Formula, None], str]:

        def polish_binary(op: str, rem: str) -> Tuple[Union[Formula, None], str]:
            first, remains_first = Formula._parse_polish(rem)
            second, remains_second = Formula._parse_polish(remains_first)
            return Formula(op, first, second), remains_second

        if string is None:
            return None, ""
        elif string[0] in ["T", "F"]:
            return Formula(string[0]), string[1:]
        elif string[0] >= "p" and string[0] <= "z":
            ind = 1
            while ind < len(string) and string[ind].isdigit():
                ind += 1
            return Formula(string[0:ind]), string[ind:]
        elif string[0] == "~":
            var, remains = Formula._parse_polish(string[1:])
            return Formula("~", var), remains
        elif string[0] in ["&", "|"]:
            return polish_binary(string[0], string[1:])
        elif string[0:2] == "->":
            return polish_binary("->", string[2:])


    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8
        form, extra = Formula._parse_polish(string)
        return form

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variable name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or \
                   is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
