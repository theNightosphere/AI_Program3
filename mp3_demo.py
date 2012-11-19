#!/usr/bin/python
import prog3v2

import sys

'(Move (Param (|x|)(|y|)(|z|))(Precon (AND (P |y|)(NOT (P |z|)))(AddList (P |z|))(DelList (P |y|)))'

def parse_input(input_s, output_file = None):
    '''Takes a file of lisp readable input and tests that output using
three preset tests. The default mode is to print the results, but if 
output_file is not None, then the results are saved to the file stream 
passed to none. Note: output_file is a file object, NOT a string.

    Keyword Arguments:
    input_s -- The lisp-readable input string to be tested.
    output_file -- The file object where results are printed (if it is not
the default None value)

    returns:
    Nothing'''

    tests = prog3v2.get_exps(input_s)
    for exp in tests:
        if(exp[1:7] == 'part_a'):
            test_a(exp, output_file)
        elif exp[1:7] == 'part_b':
            test_b(exp, output_file)
        elif exp[1:7] == 'part_c':
            test_c(exp, output_file)




def test_a(string_a, output_file):
    '''Performs the tests for part a based on the Lisp-readable input given for part a. Determines whether the given propositions are well-formed and prints out the answer.

    Keyword Arguments:
    string_a -- The string starting with '(part_a' that contains the propositions to be tested for well-formedness.
    output_file -- The file object to output results to. If this is None then
output is printed to the console

    Returns:
    Nothing.'''
    expressions_a = prog3v2.get_exps(string_a[1:-1])
    for prop in expressions_a:
        is_wf = prog3v2.wfp_checker(prop)
        if output_file is None:
            print('(part_a {} {})'.format(prop, is_wf))
        else:
            output_file.write('(part_a {} {})\n'.format(prop, is_wf))


def test_b(string_b, output_file):
    '''Extracts all the lisp-readable expressions passed as arguments in
string_b then either prints it to the console, or writes it to the file
object called output_file if it is not None.

    Keyword Arguments:
    string_b -- The lisp-readable string with the expressions to be tested
based on their truth value and whether or not they are tautologies.
    output_file -- The file object to write the results of the test to.
If no file was specified, this value is simply None.

    Returns:
    Nothing'''
    #Get the expressions and values, then get the individual expressions to be evaluated by parsing the result of the first call to get_exps once more.
    exps_and_vals = prog3v2.get_exps(string_b[1:-1])
    test_exps = exps_and_vals[0]
    truth_values = exps_and_vals[1]
    expressions_b = prog3v2.get_exps(test_exps[1:-1])
    if output_file is None:
        print('\n')
    else:
        output_file.write('\n')
    for prop in expressions_b:
        result = prog3v2.TruthValue(truth_values,prop)
        if output_file is None:
            print('(part_b {} {})'.format(prop, result))
            is_tautology = prog3v2.IsTautology(prop)
            print('(IsTautology {} {})'.format(prop,is_tautology))
        else:
            output_file.write('(part_b {} {})\n'.format(prop, result))
            is_tautology = prog3v2.IsTautology(prop)
            output_file.write('(IsTautology {} {})\n'.format(prop,is_tautology))



def test_c(string_c, output_file):
    '''Extracts all the lisp-readable expressions passed as arguments in
string_c then either prints it to the console, or writes it to the file
object called output_file if it is not None.

    Keyword Arguments:
    string_c -- The lisp-readable string with the expressions to be tested
for well-formedness in the context of FOL
    output_file -- The file object to write the results of the test to.
If no file was specified, this value is simply None.

    Returns:
    Nothing'''

    expressions_c = prog3v2.get_exps(string_c[1:-1])
    if output_file is None:
        print('\n')
    else:
        output_file.write('\n')
    for prop in expressions_c:
        is_wf = prog3v2.wfp_checkerFOL(prop)
        if output_file is None:
            print('(part_c {} {})'.format(prop, is_wf))
        else:
            output_file.write('(part_c {} {})\n'.format(prop, is_wf))

if __name__ == '__main__':
    command_input = sys.argv[1]
    print('Program 3 Demo loading from file {}.'.format(command_input))
    with open(command_input) as user_file:
        file_in = user_file.read()
        if (len(sys.argv) > 2):
            with open(sys.argv[2], 'w') as file_out:
                print('Output is being printed to {}.'.format(sys.argv[2]))
                parse_input(file_in, file_out)
        else:
            print('Output is being printed to the console.\n')
            parse_input(file_in)
