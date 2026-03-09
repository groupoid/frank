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
    clause = {:clause, 1, [], [], [generate_expr(expr, MapSet.new())]}
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

  defp generate_expr(%AST.Var{name: name}, env) do
    # Map to Erlang variable (Capitalized) or atom if it's a global
    erl_name = String.capitalize(name) |> String.to_atom()

    if MapSet.member?(env, name) do
      {:var, 1, erl_name}
    else
      {:atom, 1, erl_name}
    end
  end

  defp generate_expr(%AST.Universe{level: i}, _env) do
    {:integer, 1, i}
  end

  defp generate_expr(%AST.Lam{name: x, body: body}, env) do
    erl_x = {:var, 1, String.capitalize(x) |> String.to_atom()}
    new_env = MapSet.put(env, x)
    {:fun, 1, {:clauses, [{:clause, 1, [erl_x], [], [generate_expr(body, new_env)]}]}}
  end

  defp generate_expr(%AST.App{func: f, arg: arg}, env) do
    {:call, 1, generate_expr(f, env), [generate_expr(arg, env)]}
  end

  defp generate_expr(%AST.Constr{index: j, args: args}, env) do
    # Represent as tuple {Index, Args...}
    {:tuple, 1, [{:integer, 1, j} | Enum.map(args, &generate_expr(&1, env))]}
  end

  defp generate_expr(%AST.Let{decls: decls, body: body}, env) do
    # Generate: begin Var1 = Expr1, Var2 = Expr2, ..., Body end
    new_env = Enum.reduce(decls, env, fn {name, _}, acc -> MapSet.put(acc, name) end)

    matches =
      Enum.map(decls, fn {name, expr} ->
        {:match, 1, {:var, 1, String.capitalize(name) |> String.to_atom()},
         generate_expr(expr, new_env)}
      end)

    {:block, 1, matches ++ [generate_expr(body, new_env)]}
  end

  # Ind is the hard part - it's basically a recursive function application.
  defp generate_expr(%AST.Ind{cases: _cases, term: t}, env) do
    # Simplified: just return the term.
    # Real implementation needs to generate a recursive call or inline the induction.
    generate_expr(t, env)
  end
end
