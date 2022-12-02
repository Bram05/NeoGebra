#include "TextRenderer.h"
#include "Application.h"
#include "shader_configure.h"
#include "text_fonts_glyphs.h"
#include <ft2build.h>
#include FT_FREETYPE_H



Text::Text(int window_width, int window_height, color _color) {
	FT_Library free_type;
	const char* vert_shader_text = "./src/shader_text.vert";
	const char* frag_shader_text = "./src/shader_text.frag";

	Shader text_shader(vert_shader_text, frag_shader_text);
	text_shader.use();
	_Text textObject(free_type, window_width, window_height, "1234567890&.-abcdefghijklmnopqrstuvwxyz:_ABCDEFGHIJKLMNOPQRSTUVWXYZ ");
	unsigned int font_colour_loc = glGetUniformLocation(text_shader.ID, "font_colour");
	glUniform3fv(font_colour_loc, 1, glm::value_ptr(RGB));


}
Text::createMessage(_Text textObject, string text, int x, int y, int font_size) {
	textObject.create_text_message(text, x, y, "Text Fonts/arialbi.ttf", font_size, false);
}
Text::drawMessage(_Text textObject, int index) {
	textObject.draw_messages(index);
}
Text::drawAllMessages(_Text textObject) {
	textObject.drawMessages();
}
Text::drawLastMessage(_Text textObject) {
	messagesCount = textObject.messages.size();
	if (messagesCount >= 1) {
		textObject.draw_messages(messagesCount - 1);
	}
	else {
		std::cout << "No Messages to be drawn."
	}
	
}

Text::getColor(string preset) {
	
	switch (preset)
	
	{
	case "red":
		glm::vec3 RGB(255, 0, 0);
		break;
	
	case "green":
		glm::vec3 RGB(0, 255, 0);
		break;

	case "blue":
		glm::vec3 RGB(0, 0, 255);
		break;
	}
}

Text::~Text() {

}
