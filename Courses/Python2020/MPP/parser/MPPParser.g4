parser grammar MPPParser;

options { tokenVocab=MPPLexer; }

script
    :
    seq_instrs
    ;

seq_instrs
    :
    instr_semi*
    ;

instr_semi
    :
    docx_instr_semi
    | web_instr_semi
    ;

docx_instr_semi
    :
    // ? for supporting empty instruction
    Docx docx_instr? Semi
    ;

web_instr_semi
    :
    // ? for supporting empty instruction
    web_instr? Semi
    ;

docx_instr
    :
    create_doc
    | add_page
    | add_header
    | add_subheader
    | set_orientation
    | add_content
    | add_text
    ;

create_doc
    :
    Add docname
    ;

add_page
    :
    Add A4
    ;

add_header
    :
    Add 'h' CommonWord
    ;

add_subheader
    :
    Add 'sh' CommonWord
    ;

add_content
    :
    Add 'p' Number? img_or_caption
    ;

add_text
    :
    Add 't' CommonWord
    ;

img_or_caption
    :
    (Image | Capture | Full)
    ;


set_orientation
    :
    Landscape | Portrait
    ;

web_instr
    :
    load_url
    | loop
    ;

load_url
    :
    CommonWord
    ;

loop
    :
    Forall in_range? loop_block
    ;

in_range
    :
    '(' Number ',' Number ')'
    ;

loop_block
    :
    Open docx_instr_semi+ Close
    ;

docname
    :
    CommonWord
    ;