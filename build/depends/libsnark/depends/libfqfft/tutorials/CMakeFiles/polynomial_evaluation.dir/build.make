# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 2.8

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list

# Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/hanyun/Desktop/598NB_final/tutorial

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/hanyun/Desktop/598NB_final/tutorial/build

# Include any dependencies generated for this target.
include depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/depend.make

# Include the progress variables for this target.
include depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/progress.make

# Include the compile flags for this target's objects.
include depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/flags.make

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/flags.make
depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o: ../depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation_example.cpp
	$(CMAKE_COMMAND) -E cmake_progress_report /home/hanyun/Desktop/598NB_final/tutorial/build/CMakeFiles $(CMAKE_PROGRESS_1)
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Building CXX object depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o"
	cd /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials && /usr/bin/c++   $(CXX_DEFINES) $(CXX_FLAGS) -o CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o -c /home/hanyun/Desktop/598NB_final/tutorial/depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation_example.cpp

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.i"
	cd /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials && /usr/bin/c++  $(CXX_DEFINES) $(CXX_FLAGS) -E /home/hanyun/Desktop/598NB_final/tutorial/depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation_example.cpp > CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.i

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.s"
	cd /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials && /usr/bin/c++  $(CXX_DEFINES) $(CXX_FLAGS) -S /home/hanyun/Desktop/598NB_final/tutorial/depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation_example.cpp -o CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.s

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.requires:
.PHONY : depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.requires

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.provides: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.requires
	$(MAKE) -f depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/build.make depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.provides.build
.PHONY : depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.provides

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.provides.build: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o

# Object files for target polynomial_evaluation
polynomial_evaluation_OBJECTS = \
"CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o"

# External object files for target polynomial_evaluation
polynomial_evaluation_EXTERNAL_OBJECTS =

depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o
depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/build.make
depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation: depends/libsnark/depends/libff/libff/libff.a
depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation: /usr/lib/x86_64-linux-gnu/libgmp.so
depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation: depends/libsnark/depends/libzm.a
depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --red --bold "Linking CXX executable polynomial_evaluation"
	cd /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/polynomial_evaluation.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/build: depends/libsnark/depends/libfqfft/tutorials/polynomial_evaluation
.PHONY : depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/build

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/requires: depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/polynomial_evaluation_example.cpp.o.requires
.PHONY : depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/requires

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/clean:
	cd /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials && $(CMAKE_COMMAND) -P CMakeFiles/polynomial_evaluation.dir/cmake_clean.cmake
.PHONY : depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/clean

depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/depend:
	cd /home/hanyun/Desktop/598NB_final/tutorial/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/hanyun/Desktop/598NB_final/tutorial /home/hanyun/Desktop/598NB_final/tutorial/depends/libsnark/depends/libfqfft/tutorials /home/hanyun/Desktop/598NB_final/tutorial/build /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials /home/hanyun/Desktop/598NB_final/tutorial/build/depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : depends/libsnark/depends/libfqfft/tutorials/CMakeFiles/polynomial_evaluation.dir/depend
