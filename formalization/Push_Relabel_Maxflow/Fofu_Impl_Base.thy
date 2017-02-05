theory Fofu_Impl_Base
imports 
  "$AFP/Refine_Imperative_HOL/IICF/IICF"
  "$AFP/Refine_Imperative_HOL/Sepref_ICF_Bindings"
  "~~/src/HOL/Library/Rewrite"
  Refine_Monadic_Syntax_Sugar
begin
  hide_type (open) List_Seg.node

  interpretation Refine_Monadic_Syntax .


end
