# Expression parser

`Recognize` accepts a nonempty sequence of ASCII digit runs separated by single `+` or `-` operators. The grammar is `[0-9]+([+-][0-9]+)*`. The result is a Boolean. The code groups digits without converting their numeric values, and whitespace and unary signs are outside the grammar. [Go implementation](../examples/provable/expression_parser/expression_parser.go)

## Follow the Go pipeline

1. `Tokenize` preallocates an empty token slice with capacity equal to the input length. It tracks whether it is inside a digit run and emits one `Number` at the start of each run. An operator emits its own token and ends the run. The first invalid byte sets the validity flag to false and freezes output, so the caller receives the tokens for the valid prefix and a false flag.
2. `Parse` starts in `needNumber`. A number moves it to `afterNumber`, and an operator from that state moves it back to `needNumber`. All other transitions enter the absorbing `invalid` state. Only `afterNumber` accepts at end of input.
3. `Recognize` requires both lexical validity and token acceptance. For `12-3+45`, the tokens are `Number, Minus, Number, Plus, Number` and recognition succeeds. For `12x+3`, tokenization returns `Number` and false. The lexical flag prevents the otherwise valid token prefix from being accepted. For `12++3`, tokenization succeeds and the parser rejects the second plus.

## Read the specification and proofs

[expression_rules.lean](../examples/provable/expression_parser/expression_rules.lean) defines three recursive functions over lists. `lex` describes token output and lexical validity. `tokenGrammar` alternates between expecting a number and expecting an operator or end of input. `byteGrammar` describes the byte grammar directly, including the option to continue a digit run.

The [generated model](../examples/provable/expression_parser/expression_parser_gen.lean) represents slices with an optional list and capacity pair. The reference's `contents` treats nil as empty for grammar recognition. The tokenizer law is stronger than a check of token contents alone. It requires a present output slice with capacity equal to the input's length, including for nil input.

Read [expression_parser_proofs.lean](../examples/provable/expression_parser/expression_parser_proofs.lean) in this order:

1. `tokenizes` uses `lexFold` to relate the generated tokenizer loop to `lex`. The lemma tracks the accumulated output and its capacity. `lexStopped` shows that processing the remaining bytes after an invalid byte leaves the output frozen.
2. `parses` uses `parseFold` to relate the generated parser loop to `tokenGrammar`, with `parseStopped` handling the absorbing rejection state.
3. `recognizes` composes those laws with `lexMatches`, which connects lexical validity and token acceptance to `byteGrammar`. The end-to-end statement quantifies over the modeled input slices.

[Run the parser checks from a checkout](../CONTRIBUTING.md#check-the-expression-parser).
