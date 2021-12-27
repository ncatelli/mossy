# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar
Grammar is heavily referenced from [WMU cs4850 course grammar](https://cs.wmich.edu/%7Egupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm)

```
tranlation_unit: external_declaration*
        ;

external_declaration: function_declaration
        | var_declaration
        ;

function_declaration: type_declarator identifier '(' ')' compound_statement
        ;

compound_statement: '{' '}'
        |    '{' statement* '}'
        ;

statement: 
        | expression ';'
        | var_declaration
        | if_statement 
        | while_statement 
        | for_statement
        | return_stmt
        ;

var_declaration: type_declarator  '[' integer_literal ']' ';'
        | type_declarator identifier_list ';'
        ;

if_statement: if_head
        | if_head 'else' compound_statement 
        ;

if_head: 'if' '(' expression ')' compound_statement 
        ;

while_statement: 'while' '(' expression ')' compound_statement
        ;

for_statement: 'for' '(' preop_statement ';'
                          expression ';'
                          postop_statement ')' compound_statement  ;

preop_statement: assignment 
        ;

postop_statement: expression
        ;

return_statement: 'return' expression? ';'
        ;

expression: assignment
        ;

assignment:   identifier '=' assignment
        | equality
        ;

equality: relational ( ( '==' | '!=' ) relational )*
        ;

relational: addition ( ( '<' | '<=' | '>' | '>=' ) addition )*
        ;

addition: multiplication ( ( '-' | '+' ) multiplication )* 
        ;

multiplication: call ( ( '/' | '%' | '*' ) call )* 
        ;

call: identifier '(' expression? ')'
        | prefix_expression
        ;

prefix_expression: '*' prefix_expression
        | '&' identifier
        | primary
        ;

postfix_expression: primary
        | postfix_expression '[' expression ']'
        ;

primary: identifier
        | string_literal
        | integer_literal
        | grouping 
        ;

char:   alphabetic
        ;

grouping: '(' expression ')'
        ;

identifier_list: identifier
        | identifier ',' identifier_list
        ;

identifier: alphabetic+
        ;

type_declarator:   type_specifier optional_pointer
        ;

optional_pointer: ('*' optional_pointer)?
        ;

type_specifier: 'char'
        | 'short'
        | 'int'
        | 'long'
        | 'void'
        ;


string_literal: '"' (alphabetic | integer_literal) '"'

integer_literal:  [0-9]*;


alphabetic: [a-zA-Z]+;
```