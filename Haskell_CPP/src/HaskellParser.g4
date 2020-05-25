parser grammar HaskellParser;

options { tokenVocab=HaskellLexer; }

@parser::members {
    bool MultiWayIf = true;
    bool MagicHash  = true;
    bool FlexibleInstances = true;

    bool FunctionalDependencies = true;
    bool TypeFamilies = true;
    bool GADTs = true;
    bool StandaloneDeriving = true;
    bool DerivingVia = true;
    bool LambdaCase = true;
    bool EmptyCase  = true;
    bool RecursiveDo = true;
}

module :  semi* pragmas? semi* (module_content | body) EOF;

module_content
    :
    'module' modid exports? where_module
    ;

where_module
    :
    'where' module_body
    ;

module_body
    :
    open body close semi*
    ;

pragmas
    :
    pragma+
    ;

pragma
    :
    '{-#' 'LANGUAGE'  extension (',' extension)* '#-}' SEMI?
    ;

extension
    :
    CONID
    ;

body
    :
    (impdecls topdecls)
    | impdecls
    | topdecls
    ;

impdecls
    :
    (impdecl | NEWLINE | semi)+
    ;

exports
    :
    '(' (exprt (',' exprt)*)? ','? ')'
    ;

exprt
    :
    qvar
    | ( qtycon ( ('(' '..' ')') | ('(' (cname (',' cname)*)? ')') )? )
    | ( qtycls ( ('(' '..' ')') | ('(' (qvar (',' qvar)*)? ')') )? )
    | ( 'module' modid )
    ;

impdecl
    :
    'import' 'qualified'? modid ('as' modid)? impspec? semi+
    ;

impspec
    :
    ('(' (himport (',' himport)* ','?)? ')')
    | ( 'hiding' '(' (himport (',' himport)* ','?)? ')' )
    ;

himport
    :
    var
    | ( tycon ( ('(' '..' ')') | ('(' (cname (',' cname)*)? ')') )? )
    | ( tycls ( ('(' '..' ')') | ('(' sig_vars? ')') )? )
    ;

cname
    :
    var | con
    ;

// -------------------------------------------
// Top-Level Declarations
topdecls : (topdecl semi+| NEWLINE | semi)+;

topdecl
    :
    cl_decl
    | ty_decl
    // Check KindSignatures
    | standalone_kind_sig
    | inst_decl
    | {StandaloneDeriving}? standalone_deriving
    | ('default' '(' (type (',' type)*)? ')' )
    | ('foreign' fdecl)
    | ('{-#' 'DEPRECATED' deprecations? '#-}')
    | ('{-#' 'WARNING' warnings? '#-}')
    | ('{-#' 'RULES' rules? '#-}')
    | decl
    ;

// Type classes
cl_decl
    :
    'class' tycl_hdr fds? where_cls?
    ;

// Type declarations (toplevel)
ty_decl
    :
    // ordinary type synonyms
    ('type' type '=' ktypedoc)
    // type family declaration
    | ('type' 'family' type opt_tyfam_kind_sig opt_injective_info? where_type_family?)
    // ordinary data type or newtype declaration
    | ('data' (typecontext '=>')? simpletype ('=' constrs)? derivings?)
    | ('newtype' (typecontext '=>')? simpletype '=' newconstr derivings?)
    // GADT declaration
    | ('data' capi_ctype? tycl_hdr opt_kind_sig? gadt_constrlist? derivings?)
    | ('newtype' capi_ctype? tycl_hdr opt_kind_sig?)
    // data family
    | ('data' 'family' type opt_datafam_kind_sig?)
    ;

// standalone kind signature

standalone_kind_sig
    :
    'type' sks_vars '::' ktypedoc
    ;

// See also: sig_vars
sks_vars
    :
    oqtycon (',' oqtycon)*
    ;

inst_decl
    :
    ('instance' overlap_pragma? inst_type where_inst?)
    | ('type' 'instance' ty_fam_inst_eqn)
    // 'constrs' in the end of this rules in GHC
    // This parser no use docs
    | ('data' 'instance' capi_ctype? tycl_hdr_inst derivings?)
    | ('newtype' 'instance' capi_ctype? tycl_hdr_inst derivings?)
    // For GADT
    | ('data' 'instance' capi_ctype? tycl_hdr_inst opt_kind_sig? gadt_constrlist? derivings?)
    | ('newtype' 'instance' capi_ctype? tycl_hdr_inst opt_kind_sig? gadt_constrlist? derivings?)
    ;

overlap_pragma
    :
      '{-#' 'OVERLAPPABLE' '#-}'
    | '{-#' 'OVERLAPPING' '#-}'
    | '{-#' 'OVERLAPS' '#-}'
    | '{-#' 'INCOHERENT' '#-}'
    ;


deriv_strategy_no_via
    :
      'stock'
    | 'anyclass'
    | 'newtype'
    ;

deriv_strategy_via
    :
    'via' ktype
    ;

deriv_standalone_strategy
    :
    'stock'
    | 'anyclass'
    | 'newtype'
    | deriv_strategy_via
    ;

// Injective type families

opt_injective_info
    :
    '|' injectivity_cond
    ;

injectivity_cond
    :
    // but in GHC new tyvarid rule
    tyvarid
    | (tyvarid '->' inj_varids)
    ;

inj_varids
    :
    tyvarid+
    ;

// Closed type families

where_type_family
    :
    'where' ty_fam_inst_eqn_list
    ;

ty_fam_inst_eqn_list
    :
    (open ty_fam_inst_eqns? close)
    | ('{' '..' '}')
    | (open '..' close)
    ;

ty_fam_inst_eqns
    :
    ty_fam_inst_eqn (semi ty_fam_inst_eqn)* semi?
    ;

ty_fam_inst_eqn
    :
    'forall' tv_bndrs '.' type '=' ktype
    | type '=' ktype
    ;

//  Associated type family declarations

//  * They have a different syntax than on the toplevel (no family special
//    identifier).

//  * They also need to be separate from instances; otherwise, data family
//    declarations without a kind signature cause parsing conflicts with empty
//    data declarations.

at_decl_cls
    :
    ('data' 'family'? type opt_datafam_kind_sig?)
    | ('type' 'family'? type opt_at_kind_inj_sig?)
    | ('type' 'instance'? ty_fam_inst_eqn)
    ;

// Associated type instances
at_decl_inst
    :
    // type instance declarations, with optional 'instance' keyword
    ('type' 'instance'? ty_fam_inst_eqn)
    // data/newtype instance declaration, with optional 'instance' keyword
    | ('data' 'instance'? capi_ctype? tycl_hdr_inst constrs derivings?)
    | ('newtype' 'instance'? capi_ctype? tycl_hdr_inst constrs derivings?)
    // GADT instance declaration, with optional 'instance' keyword
    | ('data' 'instance'? capi_ctype? tycl_hdr_inst opt_kind_sig? gadt_constrlist? derivings?)
    | ('newtype' 'instance'? capi_ctype? tycl_hdr_inst opt_kind_sig? gadt_constrlist? derivings?)
    ;

// Family result/return kind signatures

opt_kind_sig
    :
    '::' kind
    ;

opt_datafam_kind_sig
    :
    '::' kind
    ;

opt_tyfam_kind_sig
    :
    ('::' kind)
    | ('=' tv_bndr)
    ;

opt_at_kind_inj_sig
    :
    ('::' kind)
    | ('=' tv_bndr '|' injectivity_cond)
    ;

tycl_hdr
    :
    (tycl_context '=>' type)
    | type
    ;

tycl_hdr_inst
    :
    ('forall' tv_bndrs '.' tycl_context '=>' type)
    | ('forall' tv_bndr '.' type) 
    | (tycl_context '=>' type)
    | type
    ;

capi_ctype
    :
    ('{-#' 'CTYPE' STRING STRING '#-}')
    | ('{-#' 'CTYPE' STRING '#-}')
    ;

// -------------------------------------------
// Stand-alone deriving

standalone_deriving
    :
    'deriving' deriv_standalone_strategy? 'instance' overlap_pragma? inst_type
    ;

// -------------------------------------------

where_inst
    :
    // In GHC decllist_inst
    'where' idecls
    ;

decls
    :
    open ((decl semi+)* decl semi*)? close
    ;

decl
    :
    '{-#' 'INLINE' qvar '#-}'
    | '{-#' 'NOINLINE' qvar '#-}'
    | '{-#' 'SPECIALIZE' specs '#-}'
    | gendecl
    | ((funlhs | pat) rhs)
    | semi+
    ;

// -------------------------------------------
// Transformation Rules

rules
    :
    pragma_rule (';' pragma_rule)* ';'?
    ;

pragma_rule
    :
    pstring rule_activation? rule_foralls? infixexp '=' exp
    ;

rule_activation_marker
    :
    '~' | varsym
    ;

rule_activation
    :
    ('[' integer ']')
    | ('[' rule_activation_marker integer ']')
    | ('[' rule_activation_marker ']')
    ;

rule_foralls
    :
    ('forall' rule_vars? '.' ('forall' rule_vars? '.')?)
    ;

rule_vars
    :
    rule_var+
    ;

rule_var
    :
    varid
    | ('(' varid '::' ctype ')')
    ;

// -------------------------------------------
// Warnings and deprecations (c.f. rules)

warnings
    :
    pragma_warning (';' pragma_warning)* ';'?
    ;

pragma_warning
    :
    namelist strings
    ;

deprecations
    :
    pragma_deprecation (';' pragma_deprecation)* ';'?
    ;

pragma_deprecation
    :
    namelist strings
    ;

strings
    :
    pstring
    | ('[' stringlist? ']')
    ;

stringlist
    :
    pstring (',' pstring)*
    ;

// -------------------------------------------

specs
    :
    spec (',' spec)*
    ;

spec
    :
    sig_vars '::' type
    ;

cdecls
    :
    open ((cdecl semi+)* cdecl semi*)? close
    ;

cdecl
    :
    gendecl
    | ((funlhs | var) rhs)
    ;

idecls
    :
    open ((idecl semi+)* idecl semi*)? close
    ;

idecl
    :
    (funlhs | var) rhs
    ;

gendecl
    :
    // vars '::' (typecontext '=>')? type
    sig_vars '::' ctype
    | (fixity (DECIMAL)? ops)
    ;

// -------------------------------------------
// Nested declaration

// Declaration in class bodies

decl_cls
    :
    at_decl_cls
    | decl
    // default rule
    ;

decls_cls
    :
    // decl_cls (semi decl_cls)* semi?
    (decl_cls semi+)* decl_cls semi*
    ;

decllist_cls
    :
    open decls_cls? close
    ;

where_cls
    :
    // In GHC decls_cls
    'where' decllist_cls
    ;

ops
    :
    op (',' op)*
    ;

fixity
    :
    'infix' | 'infixl' | 'infixr'
    ;

type
    :
    btype
    | btype '->' ctype
    ;

typedoc
    :
    btype
    | btype '->' ctypedoc
    ;

btype
    :
    tyapps
    ;

tyapps
    :
    tyapp+
    ;

tyapp
    :
    atype
    | qtyconop
    | tyvarop
    | ('\'' qconop)
    | ('\'' varop)
    | unpackedness
    ;

atype
    :
    gtycon
    | tyvar
    | '*'
    | ('{' fielddecls '}')
    | ('(' ')')
    | ('(' ktype (',' ktype)* ')')
    | ('[' ktype ']')
    | ('(' ktype ')')
    | ('[' ktype (',' ktype)* ']')
    | quasiquote
    | splice_untyped
    | ('\'' qcon_nowiredlist)
    | ('\'' '(' ktype (',' ktype)*)
    | ('\'' '[' ']')
    | ('\'' '[' ktype (',' ktype)* ']')
    | ('\'' var)
    | integer
    | STRING
    | '_'
    ;

sigtype
    :
    ctype
    ;

sigtypedoc
    :
    ctypedoc
    ;

sig_vars
    :
    var (',' var)*
    ;

// -------------------------------------------
// Types

unpackedness
    :
      ('{-#' 'UNPACK'   '#-}')
    | ('{-#' 'NOUNPACK' '#-}')
    ;

forall_vis_flag
    :
    '.'
    | '->'
    ;

// A ktype/ktypedoc is a ctype/ctypedoc, possibly with a kind annotation
ktype
    :
    ctype
    | (ctype '::' kind)
    ;

ktypedoc
    :
    ctypedoc
    | ctypedoc '::' kind
    ;

// A ctype is a for-all type
ctype
    :
    'forall' tv_bndrs forall_vis_flag ctype
    | btype '=>' ctype
    | var '::' type // not sure about this rule
    | type
    ;

ctypedoc
    :
    'forall' tv_bndrs forall_vis_flag ctypedoc
    | tycl_context '=>' ctypedoc
    | var '::' type
    | typedoc
    ;

inst_type
    :
    sigtype
    ;

deriv_types
    :
    ktypedoc (',' ktypedoc)*
    ;

// In GHC this rule is context
tycl_context
    :
    btype
    ;

tv_bndrs
    :
    tv_bndr+
    ;

tv_bndr
    :
    tyvar
    | ('(' tyvar '::' kind ')')
    ;

fds
    :
    '|' fds1
    ;

fds1
    :
    fd (',' fd)*
    ;

fd
    :
    varids0? '->' varids0?
    ;

varids0
    :
    tyvar+
    ;

kind
    :
    ctype
    ;

gadt_constrlist
    :
    'where' open gadt_constrs? semi* close
    ;

gadt_constrs
    :
    gadt_constr_with_doc (semi gadt_constr_with_doc)*
    ;

gadt_constr_with_doc
    :
    gadt_constr
    ;

gadt_constr
    :
    con_list '::' sigtypedoc
    ;

gtycon
    :
    qtycon
    | ( '(' ')' )
    | ( '[' ']' )
    | ( '(' '->' ')' )
    | ( '(' ',' '{' ',' '}' ')' )
    ;

typecontext
    :
    cls
    | ( '(' cls (',' cls)* ')' )
    ;

cls
    :
    (conid varid)
    // Flexible Context and MultiParamTypeClasses
    | (conid multiparams)
    | ( qtycls '(' tyvar (atype (',' atype)*) ')' )
    ;

multiparams
    :
    multiparam+
    ;

multiparam
    :
    qvarid
    | qconid
    ;

scontext
    :
    simpleclass
    | ( '(' (simpleclass (',' simpleclass)*)? ')' )
    ;

simpleclass
    :
    qtycls tyvar
    ;

simpletype
    :
    tycon tyvar*
    ;

constrs
    :
    constr ('|' constr)*
    ;

constr
    :
    (con ('!'? atype)*)
    | ((btype | ('!' atype)) conop (btype | ('!' atype)))
    | (con '{' (fielddecl (',' fielddecl)* )? '}')
    ;

newconstr
    :
    (con atype)
    | (con '{' var '::' type '}')
    ;

fielddecls
    :
    fielddecl (',' fielddecl)*
    ;

fielddecl
    :
    sig_vars '::' ctype
    ;

derivings
    :
    deriving+
    ;

deriving
    :
    ('deriving' deriv_clause_types)
    | ('deriving' deriv_strategy_no_via deriv_clause_types)
    | ('deriving' deriv_clause_types {DerivingVia}? deriv_strategy_via)
    ;

deriv_clause_types
    :
    qtycon
    | '(' ')'
    | '(' deriv_types ')'
    ;

inst
    :
    gtycon
    | ( '(' gtycon tyvar* ')' )
    | ( '(' gtycon tycon* ')' ) // FlexibleInstances
    | ( '(' tyvar ',' tyvar (',' tyvar)* ')')
    | ( '[' tyvar ']')
    | ( '(' tyvar '->' tyvar ')' )
    ;

// -------------------------------------------
// Foreign import and export declarations

fdecl
    :
    ('import' callconv safety? impent var '::' type)
    | ('export' callconv expent var '::' type)
    ;

callconv
    :
    'ccall' | 'stdcall' | 'cplusplus' | 'javascript'
    ;

impent : pstring;
expent : pstring;
safety : 'unsafe' | 'safe';

// -------------------------------------------

funlhs
    :
    (var apat+)
    | (pat varop pat)
    | ( '(' funlhs ')' apat+)
    ;

rhs
    :
    ('=' exp ('where' decls)?)
    | (gdrhs ('where' decls)?);

gdrhs
    :
    gdrh+
    ;

gdrh
    :
    '|' guards '=' exp
    ;

guards
    :
    guard (',' guard)*
    ;

guard
    :
    pat '<-' infixexp
    | 'let' decls
    | infixexp
    ;

quasiquote
    :
    th_quasiquote
    | th_qquasiquote
    ;

th_quasiquote
    :
    '[' varid '|'
    ;

th_qquasiquote
    :
    '[' qvarid '|'
    ;

exp
    :
    (infixexp '::' sigtype)
    | infixexp
    ;

infixexp
    :
    (lexp qop infixexp)
    | ('-' infixexp)
    | lexp
    ;

lexp
    :
    ('\\' apat+ '->' exp)
    | ('let' decls 'in' exp)
    | ({LambdaCase}? LCASE alts)
    | ('if' exp semi? 'then' exp semi? 'else' exp)
    | ({MultiWayIf}? 'if' ifgdpats)
    | ('case' exp 'of' alts)
    | ('do' stmts)
    | ({RecursiveDo}? 'mdo' stmts)
    | fexp
    ;

fexp
    :
    aexp+
    ;

aexp
    :
    qvar
    | gcon
    | literal
    | ( '(' exp ')' )
    | ( '(' exp ',' exp (',' exp)* ')' )
    | ( '[' exp (',' exp)* ']' )
    | ( '[' exp (',' exp)? '..' exp? ']' )
    | ( '[' exp '|' qual (',' qual)* ']' )
    | ( '(' infixexp qop ')' )
    | ( '(' qop infixexp ')' )
    | ( qcon '{' (fbind (',' fbind))? '}' )
    | ('{' fbind (',' fbind)* '}')+
    // Template Haskell
    | splice_untyped
    | splice_typed
    | '[|' exp '|]'
    | '[||' exp '||]'
    | '[t|' ktype '|]'
    | '[p|' infixexp '|]'
    | '[d|' cvtopbody '|]'
    | quasiquote
    ;

splice_untyped
    :
    '$' aexp
    ;

splice_typed
    :
    '$$' aexp
    ;

cvtopbody
    :
    open cvtopdecls0? close
    ;

cvtopdecls0
    :
    topdecls semi*
    ;

qual
    :
    (pat '<-' exp)
    | ('let' decls)
    | exp
    ;

alts
    :
    (open (alt semi*)+ close)
    | ({EmptyCase}? open close)
    ;

alt
    :
    (pat '->' exp ('where' decls)?)
    | (pat gdpats ('where' decls)?)
    ;

gdpats
    :
    gdpat+
    ;

// In ghc parser on GitLab second rule is 'gdpats close'
// Unclearly possible errors with this implemmentation

// Now extension is always works (follow semantic predicate in 'lexp' rule)
ifgdpats
    :
    '{' gdpats '}'
    | gdpats
    ;

gdpat
    :
    '|' guards '->' exp
    ;

stmts
    :
    open stmt* close
    ;

stmt
    :
    (qual)
    | ({RecursiveDo}? 'rec' stmts)
    | semi+
    ;

fbind
    :
    qvar '=' exp
    ;

pat
    :
    (lpat qconop pat)
    | lpat
    ;

lpat
    :
    apat
    | ('-' (integer | pfloat))
    | (gcon apat+)
    ;

apat
    :
    (var ('@' apat)?)
    | gcon
    | (qcon '{' (fpat (',' fpat)*)? '}')
    | literal
    | '_'
    | ('(' pat ')')
    | ('(' pat ',' pat (',' pat)* ')')
    | ('[' pat (',' pat)* ']')
    | ('~'apat)
    ;

fpat
    :
    qvar '=' pat
    ;

gcon
    :
    ('(' ')')
    | ('[' ']')
    | ('(' (',')+ ')')
    | qcon
    ;

con_list
    :
    con (',' con)*
    ;

namelist
    :
    name_var (',' name_var)*
    ;

name_var
    :
    var | con
    ;

var	   : varid   | ( '(' varsym ')' );
qvar   : qvarid  | ( '(' qvarsym ')');
con    : conid   | ( '(' consym ')' );
qcon   : qconid  | ( '(' gconsym ')');
varop  : varsym  | ('`' varid '`')   ;
qvarop : qvarsym | ('`' qvarid '`')	 ;
conop  : consym  | ('`' conid '`')	 ;
qconop : gconsym | ('`' qconid '`')	 ;
op     : varop   | conop			 ;
qop    : qvarop  | qconop			 ;
gconsym: ':'  	 | qconsym			 ;

qtyconop: qtyconsym | ('`' qtycon '`');
qtyconsym:qconsym | qvarsym | tyconsym;
tyconsym: consym | varsym | ':' | '-' | '.';
tyvarop: '`' tyvarid '`';

qcon_nowiredlist
    :
    qcon
    | sysdcon_nolist
    ;

sysdcon_nolist
    :
    ('(' ')')
    | ('(' ','+ ')')
    // | ('(#' '#)')
    // | ('(#' ','+ '#)')
    ;

open : VOCURLY | OCURLY;
close : VCCURLY | CCURLY;
semi : ';' | SEMI;

literal : integer | pfloat | pchar | pstring;
special : '(' | ')' | ',' | ';' | '[' | ']' | '`' | '{' | '}';


// Expand this rule later
// In GHC:
// tyvarid : VARID | special_id | 'unsafe'
//         | 'safe' | 'interruptible';

tyvarid : varid;

special_id
    : 'as'
    | 'qualified'
    | 'hiding'
    | 'export'
    | 'stdcall'
    | 'ccall'
    | 'capi'
    | 'javascript'
    | 'stock'
    | 'anyclass'
    | 'via'
    ;

varid : (VARID | special_id) ({MagicHash}? '#'*);
conid : CONID ({MagicHash}? '#'*);

symbol: ascSymbol;
ascSymbol: '!' | '#' | '$' | '%' | '&' | '*' | '+'
        | '.' | '/' | '<' | '=' | '>' | '?' | '@'
        | '\\' | '^' | '|' | '-' | '~' | ':' ;

varsym : ascSymbol+;
consym : ':' ascSymbol*;

tyvar : varid;
tycon : conid;
tycls : conid;
modid : (conid '.')* conid;

qvarid : (modid '.')? varid;
qconid : (modid '.')? conid;
qtycon : (modid '.')? tycon;
qtycls : (modid '.')? tycls;
qvarsym: (modid '.')? varsym;
qconsym: (modid '.')? consym;

oqtycon
    :
    qtycon
    | ('(' qtyconsym ')')
    ;

integer
    :
    DECIMAL
    | OCTAL
    | HEXADECIMAL
    ;


pfloat : FLOAT;
pchar  : CHAR;
pstring: STRING;
