defmodule Frank.Compiler do
  @moduledoc """
  Main entry point for the Frank compiler.
  """
  alias Frank.{Lexer, Layout, Parser, Desugar, Codegen}

  def compile_module(source, _opts \\ []) do
    with {:ok, tokens} <- Lexer.lex(source),
         resolved <- Layout.resolve(tokens),
         {:ok, ast, _rest} <- Parser.parse(resolved),
         desugared <- Desugar.desugar(ast),
         {:ok, forms} <- Codegen.generate(desugared) do
      # Typechecking is integrated in the pipeline or done before codegen
      # For now, we assume desugared AST is typechecked or will be
      case :compile.forms(forms, [:return_errors, :debug_info]) do
        {:ok, mod, bin} -> {:ok, mod, bin}
        {:error, errors, warnings} -> {:error, {:erl_compile, errors, warnings}}
      end
    else
      {:error, _} = err -> err
    end
  end

  def load_module(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end
end
