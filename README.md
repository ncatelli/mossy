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

expression: addition
        ;

addition: multiplication ( ( "-" | "+" ) multiplication )* 
        ;

multiplication: primary ( ( "/" | "*" ) primary )* 
        ;

primary: uint8
        ;

uint8:  [0-255]
        ;

identifier: alphanumeric+
        ;

alphanumeric: [a-zA-Z0-9]+
```