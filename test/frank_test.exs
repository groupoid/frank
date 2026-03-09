defmodule FrankTest do
  use ExUnit.Case
  alias Frank.Compiler

  test "compile Samples.frank" do
    source = File.read!("test/frank/Samples.frank")
    assert {:ok, mod, bin} = Compiler.compile_module(source)
    assert is_atom(mod)
    assert is_binary(bin)
  end

  test "lexer basics" do
    assert {:ok, tokens} = Frank.Lexer.lex("module Test where\n  f x = x")
    assert Enum.any?(tokens, fn t -> elem(t, 0) == :module end)
  end

  test "typechecker basics" do
    alias Frank.Typechecker
    alias Frank.AST
    env = %Typechecker.Env{ctx: [{"x", %AST.Universe{level: 0}}]}
    term = %AST.Var{name: "x"}
    assert %AST.Universe{level: 0} = Typechecker.infer(env, term)
  end

  test "W-type sample compilation" do
    source = """
    module WTest where
    data Empty =
    data Unit = tt
    data Bool = False | True
    data W A B = Sup (x:A) (f:B x -> W A B)
    """

    assert {:ok, _mod, _bin} = Compiler.compile_module(source)
  end
end
