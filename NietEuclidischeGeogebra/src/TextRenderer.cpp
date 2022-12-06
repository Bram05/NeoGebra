//#include "TextRenderer.h"
//#include "Application.h"
//#include "shader_configure.h"
//#include "text_fonts_glyphs.h"
//#include <ft2build.h>
//#include FT_FREETYPE_H
//
//Text textObject;
//
//TextC::TextC(int window_width, int window_height, std::string _color) {
//	FT_Library free_type;
//
//	const char* vert_shader_text = "./src/shader_text.vert";
//	const char* frag_shader_text = "./src/shader_text.frag";
//
//	ShaderX text_shader(vert_shader_text, frag_shader_text);
//	text_shader.use();
//
//	textObject = Text(free_type, window_width, window_height, "1234567890&.-abcdefghijklmnopqrstuvwxyz:_ABCDEFGHIJKLMNOPQRSTUVWXYZ Ͳ");
//	unsigned int font_colour_loc = glGetUniformLocation(text_shader.ID, "font_colour");
//	glUniform3fv(font_colour_loc, 1, {255,0,0}));
//}
//
//TextC::createMessage(string text, int x, int y, int font_size) {
//	textObject.create_text_message(text, x, y, "Text Fonts/arialbi.ttf", font_size, false);
//}
//TextC::drawMessage(int index) {
//	textObject.draw_messages(index);
//}
//TextC::drawAllMessages() {
//	textObject.drawMessages();
//}
//TextC::drawLastMessage() {
//	messagesCount = textObject.messages.size();
//	if (messagesCount >= 1) {
//		textObject.draw_messages(messagesCount - 1);
//	}
//	else {
//		std::cout << "No Messages to be drawn."
//	}
//
//}
//
//TextC::~TextC() {
//
//}
