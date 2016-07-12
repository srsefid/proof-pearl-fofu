theory Fofu_Impl_Base
imports 
  CAVA_Base 
  "cava/Libs/Refine_Imperative_HOL/Sepref"
  "cava/Libs/Refine_Imperative_HOL/Heaps/Array_List"
  "~~/src/HOL/Library/Rewrite"
  Refine_Monadic_Syntax_Sugar
begin
  hide_type (open) List_Seg.node

  interpretation Refine_Monadic_Syntax .


end
