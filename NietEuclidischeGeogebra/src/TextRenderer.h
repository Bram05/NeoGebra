#pragma once

#include <glad/glad.h>
#include <GLFW/glfw3.h>
#include <ft2build.h>
#include FT_FREETYPE_H

#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>

#include <vector>
#include <iostream>
#include <fstream> 

#include "shader_configure.h"
#include "text_fonts_glyphs.h"

class TextRenderer;






class Text
{

public:

	FT_Library free_type;
	Text(int window_width, int window_height, color _color);
	~Text();

	void createMessage(_Text textObject ,string text, int x, int y, int font_size);
	color getColor(string preset);
	void drawMessage(_Text textObject, int index);
	void drawLastMessage(_Text textObject);
	void drawAllMessages(_Text textObject);
	
	

};
