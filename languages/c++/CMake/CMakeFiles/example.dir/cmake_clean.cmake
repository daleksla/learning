FILE(REMOVE_RECURSE
  "CMakeFiles/example.dir/example.cpp.o"
  "lib/libexample.pdb"
  "lib/libexample.a"
)

# Per-language clean rules from dependency scanning.
FOREACH(lang CXX)
  INCLUDE(CMakeFiles/example.dir/cmake_clean_${lang}.cmake OPTIONAL)
ENDFOREACH(lang)
