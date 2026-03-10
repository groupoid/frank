defmodule Frank.Compiler do
  @moduledoc """
  Main entry point for the Frank compiler.
  """
  alias Frank.{Lexer, Layout, Parser, Desugar, Codegen, AST}

  def compile_module(source, opts \\ []) do
    with {:ok, tokens} <- Lexer.lex(source),
         resolved <- Layout.resolve(tokens),
         {:ok, ast, _rest} <- Parser.parse(resolved) do
      # Resolve imports to build the environment
      env = resolve_imports(ast, %Frank.Typechecker.Env{}, opts)
      # Add current module names to env.name_to_mod
      env = collect_local_names(ast, env)
      # Desugar using the enriched environment
      desugared = Desugar.desugar(ast, env)

      with {:ok, forms} <- Codegen.generate(desugared, env) do
        # Typechecking is integrated in the pipeline or done before codegen
        # For now, we assume desugared AST is typechecked or will be
        case :compile.forms(forms, [:return_errors, :debug_info]) do
          {:ok, mod, bin} -> {:ok, mod, bin}
          {:error, errors, warnings} -> {:error, {:erl_compile, errors, warnings}}
        end
      end
    else
      {:error, _} = err -> err
    end
  end

  defp collect_local_names(%AST.Module{name: mod_name, declarations: decls}, env) do
    new_mapping =
      Enum.reduce(decls, env.name_to_mod, fn
        %AST.DeclValue{name: n}, acc ->
          Map.put(acc, n, mod_name)

        %AST.Inductive{name: n, constrs: cs}, acc ->
          acc = Map.put(acc, n, mod_name)
          Enum.reduce(cs, acc, fn {_, cn, _}, a -> Map.put(a, cn, mod_name) end)

        _, acc ->
          acc
      end)

    %{env | name_to_mod: new_mapping}
  end

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls}, env, opts) do
    # Implicitly import Prelude if it exists and we are not in Prelude
    env =
      if mod_name != "Prelude" do
        case load_module_to_env("Prelude", env, opts) do
          {:ok, new_env} -> new_env
          _ -> env
        end
      else
        env
      end

    Enum.reduce(decls, env, fn
      {:import, name}, acc ->
        case load_module_to_env(name, acc, opts) do
          {:ok, new_env} -> new_env
          _ -> acc
        end

      _, acc ->
        acc
    end)
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    case find_module_path(mod_name) do
      {:ok, path} ->
        source = File.read!(path)

        with {:ok, tokens} <- Lexer.lex(source),
             resolved <- Layout.resolve(tokens),
             {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved) do
          # 1. Resolve imports of the sub-module first (recursive)
          env_with_imports = resolve_imports(mod, env, opts)

          # 2. Add declarations of the current module to env
          {new_defs, new_types, new_names} =
            Enum.reduce(
              mod.declarations,
              {env_with_imports.defs, env_with_imports.env, env_with_imports.name_to_mod},
              fn
                %AST.DeclValue{} = v, {d_acc, t_acc, n_acc} ->
                  current_env = %{env_with_imports | defs: d_acc, env: t_acc, name_to_mod: n_acc}
                  desugared_v = Desugar.desugar_decl(v, current_env)

                  {Map.put(d_acc, desugared_v.name, desugared_v.expr), t_acc,
                   Map.put(n_acc, desugared_v.name, mod_name)}

                %AST.DeclData{} = data, {d_acc, t_acc, n_acc} ->
                  current_env = %{env_with_imports | defs: d_acc, env: t_acc, name_to_mod: n_acc}
                  desugared_ind = Desugar.desugar_decl(data, current_env)
                  new_t_acc = Map.put(t_acc, desugared_ind.name, desugared_ind)
                  new_d_acc = add_constructors(desugared_ind, d_acc)

                  n_acc2 = Map.put(n_acc, desugared_ind.name, mod_name)

                  n_acc3 =
                    Enum.reduce(desugared_ind.constrs, n_acc2, fn {_, cn, _}, a ->
                      Map.put(a, cn, mod_name)
                    end)

                  {new_d_acc, new_t_acc, n_acc3}

                _, acc ->
                  acc
              end
            )

          {:ok, %{env_with_imports | defs: new_defs, env: new_types, name_to_mod: new_names}}
        else
          err -> {:error, err}
        end

      nil ->
        {:error, :module_not_found}
    end
  end

  def find_module_path(mod_name) do
    # Search in priv/frank and test/frank
    path1 = "priv/frank/" <> String.replace(mod_name, ".", "/") <> ".frank"
    path2 = "test/frank/" <> String.replace(mod_name, ".", "/") <> ".frank"

    cond do
      File.exists?(path1) -> {:ok, path1}
      File.exists?(path2) -> {:ok, path2}
      true -> nil
    end
  end

  defp add_constructors(ind, defs) do
    Enum.reduce(ind.constrs, defs, fn {idx, name, ty}, acc ->
      term = make_constr_term(idx, ind, ty, [])
      Map.put(acc, name, term)
    end)
  end

  defp make_constr_term(idx, ind, ty, vars) do
    case ty do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        name = if x == "_", do: "a#{length(vars)}", else: x
        %AST.Lam{name: name, domain: a, body: make_constr_term(idx, ind, b, [name | vars])}

      _ ->
        args = Enum.reverse(vars) |> Enum.map(fn n -> %AST.Var{name: n} end)
        %AST.Constr{index: idx, inductive: ind, args: args}
    end
  end

  def load_module(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end
end
