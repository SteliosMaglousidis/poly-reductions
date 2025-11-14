theory Translation_Examples
  imports "GRecToTRec"
begin

unbundle tscom_syntax and no com'_syntax and no rcom_syntax

abbreviation "fibonacci \<equiv> IF ''n''= 0 ON ''b'' THEN (''r'' ::= A (N 0)) ELSE (
                     (IF ''n''=1 ON ''b'' THEN (''r'' ::= A (N 1)) ELSE (
                          (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            TAIL ;;
                            (''r1'' ::= A (V ''r'')) ;;
                            (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            TAIL ;;
                            (''r2'' ::= A (V ''r'')) ;;
                            (''r'' ::= Plus (V ''r1'') (V ''r2''))
                            )))"


abbreviation "ackermann \<equiv> (IF ''m''=0 ON ''b'' THEN (''r'' ::= Plus (V ''n'') (N 1) ;; TAIL) ELSE 
                     (IF ''n''=0 ON ''b'' THEN (
                                    ''m'' ::= Sub (V ''m'') (N 1) ;;
                                    ''n'' ::= Plus (V ''n'') (N 1) ;;
                                    TAIL )
                                  ELSE(
                                    ''n'' ::= Sub (V ''n'') (N 1) ;;
                                    TAIL ;;
                                    ''r1'' ::= A (V ''r'') ;;
                                    ''m'' ::= Sub (V ''m'') (N 1) ;;
                                    ''n'' ::= A (V ''r1'') ;;
                                    TAIL)))"


(*Translate to intermediate representation *)

abbreviation "fibonacci_normalized \<equiv> NORM fibonacci"

abbreviation "fibonacci_tagged \<equiv> tag_tscom fibonacci_normalized"

value  "(fibonacci_tagged)" 

abbreviation "fibonacci_reci \<equiv> \<diamondop>Rec\<lbrakk> fibonacci_tagged \<rbrakk> \<Zsurj> False"
value  "(fibonacci_reci)" 

abbreviation "fibonacci_enum_rec \<equiv> *Rec\<lbrakk> fibonacci_reci \<rbrakk> \<Zsurj> 0"
value  "(fibonacci_enum_rec)" 

abbreviation "ackermann_tagged \<equiv> tag_tscom ackermann"

value  "(ackermann_tagged)" 

abbreviation "ackermann_upto1 \<equiv> UPTO\<lbrakk> ackermann_tagged \<rbrakk> 0 \<Zsurj> False"
value  "(ackermann_upto1)" 

abbreviation  "fibonacci_branches \<equiv> upto_rec_and_rest_syn_bfs fibonacci_tagged" 

value  "(fibonacci_branches)" 

abbreviation  "ackermann_branches \<equiv> switch_branches_bfs (den_tail_calls ackermann_enum)" 

value  "(ackermann_branches)" 

abbreviation  "fibonacci_term_annot \<equiv> map add_pop_skips fibonacci_branches" 

value  "(fibonacci_term_annot)" 

abbreviation  "ackermann_term_annot \<equiv> map add_pop_skips ackermann_branches" 

value  "(ackermann_term_annot)" 

abbreviation  "fibonacci_stack_coms \<equiv> map (\<lambda>x. add_stack_coms x (removeAll ''r'' (vars fibonacci)) ''pc'') fibonacci_term_annot" 

value  "(fibonacci_stack_coms)" 

abbreviation  "fibonacci_trec_branches \<equiv> map untag_tscom fibonacci_stack_coms" 

value  "(fibonacci_trec_branches)"

abbreviation  "fibonacci_switch \<equiv> switch_basic ''pc'' fibonacci_trec_branches" 

value  "(fibonacci_switch)"

abbreviation  "fibonacci_call_start \<equiv> call_start (fibonacci) ''pc'' (length fibonacci_branches) ''r''" 

value  "(fibonacci_call_start)" 

unbundle tscom_syntax and no com'_syntax and no rcom_syntax

abbreviation "fibonacci_trec_final  \<equiv> fibonacci_call_start ;; fibonacci_switch"

value  "(fibonacci_trec_final)" 


value "fibonacci_trec_final  = grec_to_trec fibonacci ''pc'' ''r''" 

value "grec_to_trec ackermann ''pc''"

abbreviation "fibonacci_tail_final \<equiv> 
                    IF ''pc'' = 0 THEN (
                                        push_many [''n'',''r1'',''r2''] ;; 
                                        (''pc'' ::= A (N 4)) ;;
                                        PUSH ''pc'' ;;
                                        (''pc'' ::= A (N 1)) 
                                 )ELSE tsSKIP ;; 
                   (IF ''pc'' = 1 THEN (
                            IF ''n''= 0 THEN (''r'' ::= A (N 0)) ;; 
                                             pop_many [''n'',''r1'',''r2''] ;; 
                                             POP ''pc'' ;;
                            tsTAIL ELSE 
                            (IF ''n''= 1 THEN (''r'' ::= A (N 1)) ;; 
                                             pop_many [''n'',''r1'',''r2''] ;; 
                                             POP ''pc'' ;;
                            tsTAIL 
                         ELSE 
                            (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            push_many [''n'',''r1'',''r2''] ;;
                            (''pc'' ::= A (N 2)) ;;
                            PUSH ''pc'' ;;
                            (''pc'' ::= A (N 1)) ;;
                            tsTAIL)) 
                   ELSE (IF ''pc''=2 THEN (
                            (''r1'' ::= A (V ''r''));;
                            (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            push_many [''n'',''r1'',''r2''] ;;
                            (''pc'' ::= A (N 3)) ;;
                            PUSH ''pc'' ;;
                            (''pc'' ::= A (N 1)) ;;
                            tsTAIL) 
                   ELSE (IF ''pc''=3 THEN (
                            (''r2'' ::= A (V ''r''));;
                            (''r'' ::= Plus (V ''r1'') (V ''r2''));; 
                            pop_many [''n'',''r1'',''r2''] ;; 
                            POP ''pc'';;
                            tsTAIL)
                   ELSE tsSKIP)))"

end