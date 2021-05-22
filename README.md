# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar
```

statements: statement*
        |   'int' identifier ';'
        |   identifier '=' expression ';'`
        ;

statement: expression ";"
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