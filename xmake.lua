set_project("short-lambda")

set_version("0.0.1")

set_allowedmodes("debug", "release")

set_languages("c++26")

add_rules("plugin.compile_commands.autoupdate", { outputdir = "." })

set_warnings("all")

add_rules("mode.release")

target("short-lambda.headeronly")
do
  set_kind("headeronly")
  add_includedirs("include", { interface = true })
  add_headerfiles("include/(*.hpp)")
end

target("short-lambda.module")
do
  set_kind("moduleonly")
  add_files("module/short-lambda.cppm", { public = true })
  add_headerfiles("module/*.hpp")
  set_policy("build.c++.modules", true)
end

function make_example(name)
  target("example." .. name, {
    kind = "binary",
    deps = "short-lambda.module",
    files = "example/" .. name .. ".cpp" })
end

make_example("moduleonly")
make_example("forwarding-noexcept")
make_example("fmap")

target("example.headeronly", {
  kind = "binary",
  deps = "short-lambda.headeronly",
  files = "example/headeronly.cpp" })