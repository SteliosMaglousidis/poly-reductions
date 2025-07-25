theory Translation_Examples
  imports "GRecToTRec"
begin

unbundle rcom_syntax and no com'_syntax and no tscom_syntax

abbreviation "fibonacci \<equiv> IF ''n''= 0 ON ''b'' THEN (''r'' ::= A (N 0)) ELSE (
                     (IF ''n''=1 ON ''b'' THEN (''r'' ::= A (N 1)) ELSE (
                          (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            RECURSE ;;
                            (''r1'' ::= A (V ''r'')) ;;
                            (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            RECURSE ;;
                            (''r2'' ::= A (V ''r'')) ;;
                            (''r'' ::= Plus (V ''r1'') (V ''r2''))
                            )))"

abbreviation "fibonacci_tagged \<equiv> tag_rcom fibonacci"

value  "(fibonacci_tagged)" 

abbreviation "fibonacci_enum \<equiv> enum_rec_calls fibonacci_tagged"

value  "(fibonacci_enum)" 

abbreviation  "fibonacci_branches \<equiv> switch_branches_bfs fibonacci_enum" 

value  "(fibonacci_branches)" 

abbreviation  "fibonacci_term_annot \<equiv> map add_pop_skips fibonacci_branches" 

value  "(fibonacci_term_annot)" 

abbreviation  "fibonacci_stack_coms \<equiv> map (\<lambda>x. add_stack_coms x (vars fibonacci) ''pc'') fibonacci_term_annot" 

value  "(fibonacci_stack_coms)" 

abbreviation  "fibonacci_trec_branches \<equiv> map untag_tscom fibonacci_stack_coms" 

value  "(fibonacci_trec_branches)"

abbreviation  "fibonacci_switch \<equiv> switch_basic ''pc'' fibonacci_trec_branches" 

value  "(fibonacci_switch)"

abbreviation  "fibonacci_call_start \<equiv> call_start (fibonacci) ''pc'' (length fibonacci_branches)" 

value  "(fibonacci_call_start)" 

unbundle tscom_syntax and no com'_syntax and no rcom_syntax

abbreviation "fibonacci_trec_final \<equiv> fibonacci_call_start ;; fibonacci_switch"

value  "(fibonacci_trec_final)" 

abbreviation "grec_to_trec c pc \<equiv> 
  (call_start c pc (length (switch_branches_bfs (enum_rec_calls (tag_rcom c))))) ;;
  (switch_basic pc
  (map untag_tscom 
  (map (\<lambda>x. add_stack_coms x (vars c) pc)
  (map add_pop_skips 
  (switch_branches_bfs 
  (enum_rec_calls 
  (tag_rcom c)))))))"

value "fibonacci_trec_final = grec_to_trec fibonacci ''pc''" 


abbreviation "fibonacci_tail_final \<equiv> 
                    IF ''pc'' = 0 THEN (
                                        push_many [''n'',''r'',''r1'',''r2''] ;; 
                                        (''pc'' ::= A (N 4)) ;;
                                        PUSH ''pc'' ;;
                                        (''pc'' ::= A (N 1)) 
                                 )ELSE tsSKIP ;; 
                   (IF ''pc'' = 1 THEN (
                            IF ''n''= 0 THEN (''r'' ::= A (N 0)) ;; 
                                             pop_many [''n'',''r'',''r1'',''r2''] ;; 
                                             POP ''pc'' ;;
                            tsTAIL ELSE 
                            (IF ''n''= 1 THEN (''r'' ::= A (N 1)) ;; 
                                             pop_many [''n'',''r'',''r1'',''r2''] ;; 
                                             POP ''pc'' ;;
                            tsTAIL 
                         ELSE 
                            (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            push_many [''n'',''r'',''r1'',''r2''] ;;
                            (''pc'' ::= A (N 2)) ;;
                            PUSH ''pc'' ;;
                            (''pc'' ::= A (N 1)) ;;
                            tsTAIL)) 
                   ELSE (IF ''pc''=2 THEN (
                            (''r1'' ::= A (V ''r''));;
                            (''n'' ::= Sub (V ''n'') (N 1)) ;;
                            push_many [''n'',''r'',''r1'',''r2''] ;;
                            (''pc'' ::= A (N 3)) ;;
                            PUSH ''pc'' ;;
                            (''pc'' ::= A (N 1)) ;;
                            tsTAIL) 
                   ELSE (IF ''pc''=3 THEN (
                            (''r2'' ::= A (V ''r''));;
                            (''r'' ::= Plus (V ''r1'') (V ''r2''));; 
                            pop_many [''n'',''r'',''r1'',''r2''] ;; 
                            POP ''pc'';;
                            tsTAIL)
                   ELSE tsSKIP)))"

end