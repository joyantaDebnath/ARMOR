# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
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
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD

# Include any dependencies generated for this target.
include CMakeFiles/test_support_lib.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include CMakeFiles/test_support_lib.dir/compiler_depend.make

# Include the progress variables for this target.
include CMakeFiles/test_support_lib.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/test_support_lib.dir/flags.make

CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o: CMakeFiles/test_support_lib.dir/flags.make
CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o: ../crypto/test/abi_test.cc
CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o: CMakeFiles/test_support_lib.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o -MF CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o.d -o CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o -c /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/abi_test.cc

CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/abi_test.cc > CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.i

CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/abi_test.cc -o CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.s

CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o: CMakeFiles/test_support_lib.dir/flags.make
CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o: ../crypto/test/file_test.cc
CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o: CMakeFiles/test_support_lib.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o -MF CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o.d -o CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o -c /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/file_test.cc

CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/file_test.cc > CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.i

CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/file_test.cc -o CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.s

CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o: CMakeFiles/test_support_lib.dir/flags.make
CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o: ../crypto/test/test_util.cc
CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o: CMakeFiles/test_support_lib.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o -MF CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o.d -o CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o -c /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/test_util.cc

CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/test_util.cc > CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.i

CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/test_util.cc -o CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.s

CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o: CMakeFiles/test_support_lib.dir/flags.make
CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o: ../crypto/test/wycheproof_util.cc
CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o: CMakeFiles/test_support_lib.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o -MF CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o.d -o CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o -c /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/wycheproof_util.cc

CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/wycheproof_util.cc > CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.i

CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/crypto/test/wycheproof_util.cc -o CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.s

# Object files for target test_support_lib
test_support_lib_OBJECTS = \
"CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o" \
"CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o" \
"CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o" \
"CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o"

# External object files for target test_support_lib
test_support_lib_EXTERNAL_OBJECTS =

libtest_support_lib.a: CMakeFiles/test_support_lib.dir/crypto/test/abi_test.cc.o
libtest_support_lib.a: CMakeFiles/test_support_lib.dir/crypto/test/file_test.cc.o
libtest_support_lib.a: CMakeFiles/test_support_lib.dir/crypto/test/test_util.cc.o
libtest_support_lib.a: CMakeFiles/test_support_lib.dir/crypto/test/wycheproof_util.cc.o
libtest_support_lib.a: CMakeFiles/test_support_lib.dir/build.make
libtest_support_lib.a: CMakeFiles/test_support_lib.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Linking CXX static library libtest_support_lib.a"
	$(CMAKE_COMMAND) -P CMakeFiles/test_support_lib.dir/cmake_clean_target.cmake
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_support_lib.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/test_support_lib.dir/build: libtest_support_lib.a
.PHONY : CMakeFiles/test_support_lib.dir/build

CMakeFiles/test_support_lib.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/test_support_lib.dir/cmake_clean.cmake
.PHONY : CMakeFiles/test_support_lib.dir/clean

CMakeFiles/test_support_lib.dir/depend:
	cd /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD /home/joyanta/Desktop/temp_running/ARMOR/evaluation/End_to_end_application/modified_boringssl/BUILD/CMakeFiles/test_support_lib.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/test_support_lib.dir/depend

