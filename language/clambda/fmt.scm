(define-module (language clambda fmt)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-6)
  #:use-module (srfi srfi-13)
  #:use-module (srfi srfi-4)
  #:use-module (srfi srfi-69)
  #:use-module (ice-9 rdelim)
  ;;#:use-module (ice-9 optargs)

  #:export (
    ;;fmt
    new-fmt-state
    fmt fmt-start fmt-if fmt-capture fmt-let fmt-bind fmt-null
    fmt-ref fmt-set! fmt-add-properties! fmt-set-property!
    fmt-col fmt-set-col! fmt-row fmt-set-row!
    fmt-radix fmt-set-radix! fmt-precision fmt-set-precision!
    fmt-properties fmt-set-properties! fmt-width fmt-set-width!
    fmt-writer fmt-set-writer! fmt-port fmt-set-port!
    fmt-decimal-sep fmt-set-decimal-sep!
    copy-fmt-state
    fmt-file fmt-try-fit cat apply-cat nl fl nl-str
    fmt-join fmt-join/last fmt-join/dot
    fmt-join/prefix fmt-join/suffix fmt-join/range
    pad pad/right pad/left pad/both trim trim/left trim/both trim/length
    fit fit/left fit/both tab-to space-to wrt wrt/unshared dsp
    pretty pretty/unshared slashified maybe-slashified
    num num/si num/fit num/comma radix fix ellipses
    upcase downcase titlecase pad-char comma-char decimal-char
    with-width wrap-lines fold-lines justify
    make-string-fmt-transformer
    make-space make-nl-space display-to-string write-to-string
    fmt-columns columnar line-numbers
    mantissa+exponent

    ;;fmt-c
    fmt-in-macro? fmt-expression? fmt-return? fmt-default-type
    fmt-newline-before-brace? fmt-braceless-bodies?
    fmt-indent-space fmt-switch-indent-space fmt-op fmt-gen
    c-in-expr c-in-stmt c-in-test
    c-paren c-maybe-paren c-type c-literal? c-literal char->c-char
    c-struct c-union c-class c-enum c-typedef c-cast
    c-expr c-expr/sexp c-apply c-op c-indent c-current-indent-string
    c-wrap-stmt c-open-brace c-close-brace
    c-block c-braced-block c-begin
    c-fun c-var c-prototype c-param c-param-list
    c-while c-for c-if c-switch
    c-case c-case/fallthrough c-default
    c-break c-continue c-return c-goto c-label
    c-static c-const c-extern c-volatile c-auto c-restrict c-inline
    c++ c-- c+ c- c* c/ c% c& c^ c~ c! c&& c<< c>> c== c!= ;  |c\||  |c\|\||
    c< c> c<= c>= c= c+= c-= c*= c/= c%= c&= c^= c<<= c>>= ;++c --c ;  |c\|=|
    c++/post c--/post c. c-> c-sizeof
    c-bit-or c-or c-bit-or=
    cpp-if cpp-ifdef cpp-ifndef cpp-elif cpp-endif cpp-undef
    cpp-include cpp-define cpp-wrap-header cpp-pragma cpp-line
    cpp-error cpp-warning cpp-stringify cpp-sym-cat
    c-comment c-block-comment c-attribute
    %fun %array %pointer
    
    ;;fmt color
    fmt-red fmt-blue fmt-green fmt-cyan fmt-yellow fmt-magenta fmt-white
    fmt-black fmt-bold fmt-underline fmt-color fmt-in-html    
    ))

(include-from-path "language/clambda/fmt-0.8/let-optionals.scm")
(include-from-path "language/clambda/fmt-0.8/make-eq-table.scm")
(include-from-path "language/clambda/fmt-0.8/mantissa.scm")
(include-from-path "language/clambda/fmt-0.8/fmt.scm")
(include-from-path "language/clambda/fmt-0.8/fmt-pretty.scm")
(include-from-path "language/clambda/fmt-0.8/fmt-column.scm")
(include-from-path "language/clambda/fmt-0.8/fmt-c.scm")
(include-from-path "language/clambda/fmt-0.8/fmt-color.scm")



