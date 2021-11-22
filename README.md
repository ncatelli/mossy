# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar

```
program: function_declaration*
        ;

function_declaration: type identifier '(' ')' compound_statement
        ;

compound_statement: '{' '}'
        |    '{' statement* '}'
        ;

statement: 
        | expression ';'
        | declaration ';'
        | assignment ';'
        | if_statement 
        | while_statement 
        | for_statement
        | return_stmt ';'
        ;

declaration:   type identifier
        ;

assignent:   identifier '=' expression 
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

return_statement: 'return' expression?   ;

expression: equality
        ;

equality: relational ( ( '==' | '!=' ) relational )*
        ;

relational: addition ( ( '<' | '<=' | '>' | '>=' ) addition )*
        ;

addition: multiplication ( ( '-' | '+' ) multiplication )* 
        ;

multiplication: primary ( ( '/' | '*' ) primary )* 
        ;

primary: call
        | identifier
        | integer
        ;

char:   alphabetic
        ;

identifier: alphabetic+
        ;

call: identifier '(' expression? ')'
        ;

type:   integer_type
        | 'void'
        ;

integer_type:
        'char'
        | 'short'
        | 'int'
        | 'long'
        ;


integer:  [0-9]*;

alphabetic: [a-zA-Z]+;
```