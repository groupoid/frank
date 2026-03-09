defmodule Frank.AST do
  @moduledoc """
  Abstract Syntax Tree structures for the Frank compiler.
  """

  # --- Surface Language Declarations ---

  defmodule Module do
    defstruct [:name, :declarations]
  end

  defmodule DeclValue do
    defstruct [:name, :binders, :expr, :guards, :where_decls]
  end

  defmodule DeclTypeSignature do
    defstruct [:name, :type]
  end

  defmodule DeclData do
    defstruct [:name, :params, :constructors]
  end

  defmodule DeclForeign do
    defstruct [:name, :type, :erl_mod, :erl_func]
  end

  defmodule Case do
    defstruct [:expr, :branches]
  end

  defmodule Lambda do
    defstruct [:binders, :body]
  end

  # --- Core Language Terms (CIC) ---

  defmodule Var do
    defstruct [:name]
  end

  defmodule Universe do
    defstruct [:level]
  end

  defmodule Pi do
    defstruct [:name, :domain, :codomain]
  end

  defmodule Lam do
    defstruct [:name, :domain, :body]
  end

  defmodule App do
    defstruct [:func, :arg]
  end

  defmodule Inductive do
    defstruct [:name, :params, :level, :constrs]
  end

  defmodule Let do
    defstruct [:decls, :body]
  end

  # Constructor implementation: index, inductive definition, and arguments
  defmodule Constr do
    defstruct [:index, :inductive, :args]
  end

  # Induction operator: inductive definition, motive (P), cases, and target term
  defmodule Ind do
    defstruct [:inductive, :motive, :cases, :term]
  end

  # Helper for surface binders
  defmodule BinderVar do
    defstruct [:name]
  end

  defmodule BinderConstructor do
    defstruct [:name, :args]
  end

  # --- Pretty Printing ---

  def to_string(term) do
    case term do
      %Var{name: name} ->
        name

      %Universe{level: l} ->
        "U#{l}"

      %Pi{name: x, domain: a, codomain: b} ->
        "(#{x} : #{Frank.AST.to_string(a)}) -> #{Frank.AST.to_string(b)}"

      %Lam{name: x, body: b} ->
        "\\#{x} -> #{Frank.AST.to_string(b)}"

      %App{func: f, arg: a} ->
        f_str =
          case f do
            %Lam{} -> "(#{Frank.AST.to_string(f)})"
            _ -> Frank.AST.to_string(f)
          end

        a_str =
          case a do
            %App{} -> "(#{Frank.AST.to_string(a)})"
            %Lam{} -> "(#{Frank.AST.to_string(a)})"
            _ -> Frank.AST.to_string(a)
          end

        "#{f_str} #{a_str}"

      %Inductive{name: name, params: params} ->
        if params == [] do
          name
        else
          params_str = Enum.map_join(params, " ", fn {n, _} -> n end)
          "(#{name} #{params_str})"
        end

      %Constr{index: i, inductive: d, args: args} ->
        # Try to find constructor name from inductive definition
        name =
          case Enum.find(d.constrs, fn {idx, _, _} -> idx == i end) do
            {_, n, _} -> n
            _ -> "Constr#{i}"
          end

        if args == [] do
          name
        else
          "(#{name} " <> Enum.map_join(args, " ", &Frank.AST.to_string/1) <> ")"
        end

      %Ind{inductive: d, term: t} ->
        "ind_#{d.name}(#{Frank.AST.to_string(t)})"

      %Let{decls: decls, body: body} ->
        decls_str =
          Enum.map_join(decls, "; ", fn {name, expr} ->
            "#{name} = #{Frank.AST.to_string(expr)}"
          end)

        "let #{decls_str} in #{Frank.AST.to_string(body)}"

      _ ->
        inspect(term)
    end
  end
end
