#pragma once

#include <glad/glad.h>
#include <GLFW/glfw3.h>
#include <ft2build.h>
#include FT_FREETYPE_H

#include "glm/glm.hpp"
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>

#include <vector>
#include <iostream>
#include <fstream> 

#include "shader_configure.h"
#include "text_fonts_glyphs.h"

class TextC
{

public:

	FT_Library free_type;
	TextC(int window_width, int window_height, std::string _color);
	~TextC();

	void createMessage(std::string text, int x, int y, int font_size);
	
	void drawMessage( int index);
	void drawLastMessage();
	void drawAllMessages();
};
