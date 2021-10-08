# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar
```

compound_statement: '{' '}'
        |    '{' statement* '}'
        ;

statement: 
        | expression ";"
        | declaration ";"
        | assignment ";"
        | if_statement 
        | while_statement 
        ;

declaration:   'int' identifier
        ;

assignent:   identifier '=' expression 
        ;

if_statement: if_head
        | if_head 'else' compound_statement  ;

if_head: 'if' '(' expression ')' compound_statement 
        ;

while_statement: 'while' '(' expression ')' compound_statement
        ;

for_statement: 'for' '(' preop_statement ';'
                          true_false_expression ';'
                          postop_statement ')' compound_statement  ;

preop_statement: statement 
        ;

postop_statement: statement
        ;


expression: equality
        ;

equality: relational ( ( "==" | "!=" ) relational )*
        ;

relational: addition ( ( "<" | "<=" | ">" | ">=" ) addition )*
        ;

addition: multiplication ( ( "-" | "+" ) multiplication )* 
        ;

multiplication: primary ( ( "/" | "*" ) primary )* 
        ;

primary: identifier
        | uint8
        ;

uint8:  [0-255]
        ;

identifier: alphabetic+
        ;

alphabetic: [a-zA-Z]+
```