grammar Data;

file
locals [int pred_ws, int after_ws]
    :
    ( {$pred_ws = 0;} (sep {$pred_ws = $sep.cnt_ws;})? group [$pred_ws] sep_group )*
    ;

group [ int cur_ws ]
    :
    ID ( seq_id | endl_id [$cur_ws] )*
    ;

seq_id
    :
    (sep ID)* sep ID sep?
    ;

endl_id [ int cur_ws ]
locals [ int ws = 0 ]
    :
    NEWLINE sep {$ws = $sep.cnt_ws;} {$ws > $cur_ws}? seq_id
    ;

sep 
returns [ int cnt_ws ]
locals [ int tmp_cnt = 0 ]
    :
    (TAB {$tmp_cnt+=4;} | WS {$tmp_cnt+=1;})+
    {$cnt_ws = $tmp_cnt;}
    ;

sep_group
    :
    NEWLINE*
    ;

ID  : [a-z]+;
TAB : '\t'  ;
WS  : ' '   ;
NEWLINE : '\n';
    