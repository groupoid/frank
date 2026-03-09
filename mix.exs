defmodule Frank.MixProject do
  use Mix.Project

  def project do
    [
      app: :frank,
      version: "0.3.9",
      description: "The Frank Programming Language",
      deps: deps(),
      package: package()
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  def deps do
    [
      {:ex_doc, ">= 0.0.0", only: :dev}
    ]
  end

  def package() do
    [
      files: ["lib", "priv", "src", "test", "LICENSE", "README.md"],
      licenses: ["ISC"],
      maintainers: ["Namdak Tonpa"],
      name: :frank,
      links: %{"GitHub" => "https://github.com/synrc/frank"}
    ]
  end
end
