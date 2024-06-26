set_project("short-lambda")

set_version("0.0.1")

set_allowedmodes("debug", "release")

set_languages("c++26")

set_warnings("all")

-- set_toolchains("clang-18")

add_rules("mode.release")

target("short-lambda")
    set_kind("headeronly")
    add_includedirs("inc", {interface = true})
    add_headerfiles("inc/(*.hpp)")

target("example")
    set_kind("binary")
    add_deps("short-lambda")
    add_files("example/example1.cpp")