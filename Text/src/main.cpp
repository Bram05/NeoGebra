#include <glad/glad.h>
#include <GLFW/glfw3.h>

#include <ft2build.h> // https://freetype.org/freetype2/docs/tutorial/step1.html#section-1
#include FT_FREETYPE_H


#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>

#include <vector>
#include <iostream>
#include <fstream> 

#include "shader_configure.h"
#include "text_fonts_glyphs.h"

int main()
{
	// (1) GLFW: Initialise & Configure
	// ------------------------------------ -----
	if (!glfwInit())
		exit(EXIT_FAILURE);

	glfwWindowHint(GLFW_SAMPLES, 4); // Anti-aliasing
	glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
	glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 2);
	glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);

	const GLFWvidmode* mode = glfwGetVideoMode(glfwGetPrimaryMonitor());

	int monitor_width = mode->width; // Monitor's width and height.
	int monitor_height = mode->height;

	int window_width = (int)(monitor_width * 0.75); // Example: monitor_width * 0.5f... will be 50% the monitor's size.
	int window_height = (int)(monitor_height * 0.75); // Cast is simply to silence the compiler warning.

	GLFWwindow* window = glfwCreateWindow(window_width, window_height, "Text Testing", NULL, NULL);
	// GLFWwindow* window = glfwCreateWindow(window_width, window_height, "FreeType Fonts - Glyphs Text (3D Animation)", glfwGetPrimaryMonitor(), NULL); // Full Screen Mode ("Alt" + "F4" to Exit!)

	if (!window)
	{
		glfwTerminate();
		exit(EXIT_FAILURE);
	}
	glfwMakeContextCurrent(window); // Set the window to be used and then centre that window on the monitor. 
	glfwSetWindowPos(window, (monitor_width - window_width) / 2, (monitor_height - window_height) / 2);

	glfwSwapInterval(1); // Set VSync rate 1:1 with monitor's refresh rate.

	// (2) GLAD: Load OpenGL Function Pointers
	// -------------------------------------------------------
	if (!gladLoadGLLoader((GLADloadproc)glfwGetProcAddress)) // For GLAD 2 use the following instead: gladLoadGL(glfwGetProcAddress)
	{
		glfwTerminate();
		exit(EXIT_FAILURE);
	}
	glEnable(GL_MULTISAMPLE); // Anti-aliasing
	glEnable(GL_BLEND); // GL_BLEND for OpenGL transparency which is further set within the fragment shader. 
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

	// (3) Compile Shaders & Initialise Camera 
   // -----------------------------------------------------

	const char* vert_shader_text = "./src/shader_text.vert";
	const char* frag_shader_text = "./src/shader_text.frag";

	Shader text_shader(vert_shader_text, frag_shader_text);
	text_shader.use();

	// (4) Initialise FreeType & Declare Text Objects
	// -----------------------------------------------------------
	// "How is it possible that the HorizontalAdvance of a glyph is smaller than the glyph's width?"
	// https://stackoverflow.com/questions/45304838/how-is-it-possible-that-the-horizontaladvance-of-a-glyph-is-smaller-than-the-gly	

	FT_Library free_type;
	FT_Error error_code = FT_Init_FreeType(&free_type);

	if (error_code)
	{
		std::cout << "\n   Error code: " << error_code << " --- " << "An error occurred during initialising the FT_Library";
		int keep_console_open;
		std::cin >> keep_console_open;
	}

	Text text_object1(free_type, window_width, window_height, "1234567890&.-abcdefghijklmnopqrstuvwxyz:_ABCDEFGHIJKLMNOPQRSTUVWXYZ "); // Pass a specific alphabet to be used for this specific text object.
	//text_object1.create_text_message("Using OpenGL and the FreeType library to render", 110, 60, "Text Fonts/arialbi.ttf", 70, false);
	text_object1.create_text_message("Roses are red, violets are blue", 110, 40, "Text Fonts/arialbi.ttf", 70, false);

	glUniform1i(glGetUniformLocation(text_shader.ID, "alphabet_texture"), 31);

	glm::vec3 RGB(125, 125, 125);
	unsigned int font_colour_loc = glGetUniformLocation(text_shader.ID, "font_colour");
	glUniform3fv(font_colour_loc, 1, glm::value_ptr(RGB));

	while (!glfwWindowShouldClose(window)) // Main-Loop
	{

		// (7) Clear the Screen & Depth Buffer
		// ----------------------------------------------
		glClearColor(0, 0, 0, 1.0f); // This line can be moved to before the while loop.
		glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);



		text_object1.draw_messages(0);

		glfwSwapBuffers(window);
		glfwPollEvents();
	}

	// (9) Exit the Application
	// ------------------------------
	// FT_Done_Face(text_object1.face);
	FT_Done_Face(text_object1.face);
	FT_Done_FreeType(free_type);
	glDeleteProgram(text_shader.ID);

	/* glfwDestroyWindow(window) // Call this function to destroy a specific window */
	glfwTerminate(); // Destroys all remaining windows and cursors, restores modified gamma ramps, and frees resources.

	exit(EXIT_SUCCESS); // Function call: exit() is a C/C++ function that performs various tasks to help clean up resources.
}