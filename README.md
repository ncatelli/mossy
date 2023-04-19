# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Running

```bash
$ cargo build && ./target/debug/mossy -i <file>
```

## Flamegraph

```
cargo flamegraph -- ./target/debug/mossy -i <file>
```

## Pre-Processor
The pre-processor provides for text replacement prior to parsing any context sensitive grammar.

### Grammar
```
comments: (inline_comment
        | block_comment
        | character)*
        ;

block_comment: '/*' character* '*/'
        ;

inline_comment: '//' character* '\n'
        ;
```

## Parser
### Grammar
Grammar is heavily referenced from [WMU cs4850 course grammar](https://cs.wmich.edu/%7Egupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm)

```
tranlation_unit: external_declaration*
        ;

external_declaration: function_definition 
        | function_prototype ';'
        | var_declaration
        ;

function_prototype: type_declarator identifier '(' ((type_declarator identifier,)* type_declarator identifier) | (type_declarator identifier) ')'
        ;

function_definition: function_prototype compound_statement
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

var_declaration: type_declarator  '[' digit ']' ';'
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
        | logical
        ;

logical: bitwise ( ( '||' | '&&' ) bitwise )*
        ;

bitwise: equality ( ( '|' | '^' | '&' ) equality )*
        ;

equality: relational ( ( '==' | '!=' ) relational )*
        ;

relational: bitwise_shift ( ( '<' | '<=' | '>' | '>=' ) bitwise_shift )*
        ;

bitwise_shift: addition ( ( '<<' | '>>' ) addition )*
        ;

addition: multiplication ( ( '-' | '+' ) multiplication )* 
        ;

multiplication: call ( ( '/' | '%' | '*' ) call )* 
        ;

call: identifier type_declarator identifier '(' ((expression,)* expression) | expression? ')' 
        | prefix_expression
        ;

prefix_expression: '*' prefix_expression
        | '&' identifier
        | '++' prefix_expression
        | '--' prefix_expression
        | '!' prefix_expression
        | '-' prefix_expression
        | '~' prefix_expression
        | post_increment_decrement_expression 
        ;

post_increment_decrement_expression: postfix_expression '++'
        | postfix_expression '--'
        | postfix_expression
        ;

postfix_expression: identifier '[' expression ']'
        | primary
        ;

primary: identifier
        | string_literal
        | digit
        | char
        | grouping 
        ;

char:   ascii_alphabetic
        ;

char_literal: '\'' ascii_alphabetic '\''
        ;


grouping: '(' expression ')'
        ;

identifier_list: identifier
        | identifier ',' identifier_list
        ;

identifier: ( ascii_alphabetic | numeric | '_' )+
        ;

type_declarator:   type_specifier optional_pointer
        ;

optional_pointer: ('*' optional_pointer)?
        ;

type_specifier: 'char'
        | 'short int'
        | 'short'
        | 'int'
        | 'long long int'
        | 'long long'
        | 'long int'
        | 'long'
        | 'void'
        ;

string_literal: '"' ( ascii_alphanumeric | ' ' | ascii_whitespace | ascii_control | '\"' )* '"'

digit:  [0-9]*;

ascii_alphabetic: [a-zA-Z]+;

ascii_alphanumeric: ascii_alphabetic
        | digit
        ;

ascii_whitespace: *DEVNOTE: ascii check spec*
        ;

ascii_control: *DEVNOTE: ascii check spec*
        ;

space: ' '
```

#### Replacement-Grammar
The grammar for the rewrite can be found at [grammar.ebnf](./docs/grammar.ebnf). Additionally this includes an [xhtml version](./docs/grammar.xhtml) for viewing in a browser. This was directly generated from [grammar.ebnf](./docs/grammar.ebnf) with [rr](https://githug.com/ncatelli/rr-docker.git).
