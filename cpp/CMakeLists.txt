
project(EBS)
set(CMAKE_CXX_STANDARD 20)
add_executable(Test main.cpp)

target_link_libraries(Test PUBLIC -lpthread -latomic)
