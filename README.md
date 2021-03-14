# mossy
A C-frontend built around cranelift.

## Grammar
```
expression: number
          | expression '*' expression
          | expression '/' expression
          | expression '+' expression
          | expression '-' expression
          ;

number:  INTLITERAL
         ;
```