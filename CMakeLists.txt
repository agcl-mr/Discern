project(Disc_shape)
set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
cmake_minimum_required (VERSION 2.6)


find_package(CGAL QUIET COMPONENTS Core )
  include( ${CGAL_USE_FILE} )

  include_directories (BEFORE "../../include")

find_package(OpenGL REQUIRED)
include_directories(${OPENGL_INCLUDE_DIR})

find_package(GLUT REQUIRED)
include_directories(${GLUT_INCLUDE_DIR})

add_executable(Disc_shape Disc_shape.cpp)
target_compile_features(Disc_shape PRIVATE cxx_range_for)
target_link_libraries(Disc_shape ${GLUT_LIBRARY} ${OPENGL_LIBRARY})   
target_link_libraries(Disc_shape ${CGAL_LIBRARIES} ${CGAL_3RD_PARTY_LIBRARIES})                               
