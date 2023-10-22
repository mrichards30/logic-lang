import Lake
open Lake DSL

package «logic_lang» where
  -- add package configuration options here

lean_lib «LogicLang» where
  -- add library configuration options here

@[default_target]
lean_exe «logiclang» where
  root := `LogicLang