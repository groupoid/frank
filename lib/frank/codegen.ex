defmodule Frank.Codegen do
  @moduledoc """
  Translates Frank.AST into Erlang Abstract Format.
  """
  alias Frank.AST

  def generate(%AST.Module{name: mod_name, declarations: decls}) do
    current_mod = String.to_atom(mod_name)
    functions = Enum.flat_map(decls, &generate_decl/1)

    module_attr = {:attribute, 1, :module, current_mod}
    export_all = {:attribute, 1, :compile, :export_all}

    forms = [module_attr, export_all] ++ functions ++ [{:eof, 1}]
    {:ok, forms}
  end

  defp generate_decl(%AST.DeclValue{name: name, expr: expr}) do
    clause = {:clause, 1, [], [], [generate_expr(expr)]}
    [{:function, 1, String.to_atom(name), 0, [clause]}]
  end

  defp generate_decl(%AST.DeclForeign{name: name, erl_mod: mod, erl_func: func, type: _ty}) do
    # For now, simple arity extraction. Type should have arity.
    # Assume arity 1 for now.
    args = [{:var, 1, :X1}]

    call =
      {:call, 1, {:remote, 1, {:atom, 1, String.to_atom(mod)}, {:atom, 1, String.to_atom(func)}},
       args}

    [{:function, 1, String.to_atom(name), 1, [{:clause, 1, args, [], [call]}]}]
  end

  defp generate_decl(_), do: []

  defp generate_expr(%AST.Var{name: name}) do
    # Map to Erlang variable (Capitalized) or atom if it's a global
    {:var, 1, String.capitalize(name) |> String.to_atom()}
  end

  defp generate_expr(%AST.Universe{level: i}) do
    {:integer, 1, i}
  end

  defp generate_expr(%AST.Lam{name: x, body: body}) do
    erl_x = {:var, 1, String.capitalize(x) |> String.to_atom()}
    {:fun, 1, {:clauses, [{:clause, 1, [erl_x], [], [generate_expr(body)]}]}}
  end

  defp generate_expr(%AST.App{func: f, arg: arg}) do
    {:call, 1, generate_expr(f), [generate_expr(arg)]}
  end

  defp generate_expr(%AST.Constr{index: j, args: args}) do
    # Represent as tuple {Index, Args...}
    {:tuple, 1, [{:integer, 1, j} | Enum.map(args, &generate_expr/1)]}
  end

  defp generate_expr(%AST.Let{decls: _decls, body: body}) do
    # Simplified: just return the body term.
    # Real implementation needs named funs for recursiveness or match blocks.
    generate_expr(body)
  end

  # Ind is the hard part - it's basically a recursive function application.
  defp generate_expr(%AST.Ind{cases: _cases, term: t}) do
    # Simplified: just return the term.
    # Real implementation needs to generate a recursive call or inline the induction.
    generate_expr(t)
  end
end
