#pragma once // https://docs.microsoft.com/en-us/windows/win32/gdi/raster--vector--truetype--and-opentype-fonts

class Text
{
private:
	struct Alphabet_Characters
	{
		float left_bearing = 0.0f;
		float bottom_bearing = 0.0f;
		float height_plus_padding = 0.0f;
		float width_plus_padding = 0.0f;
		float glyph_advance_x = 0.0f;

		char character;

		glm::vec2 texcoord_top_left;
		glm::vec2 texcoord_top_right;
		glm::vec2 texcoord_bottom_left;
		glm::vec2 texcoord_bottom_right;
	};

	struct Message_Characters
	{
		glm::vec4 bottom_left_tr1; // Triangle 1
		glm::vec4 bottom_right_tr1;
		glm::vec4 top_left_tr1;

		glm::vec4 top_left_tr2; // Triangle 2
		glm::vec4 top_right_tr2;
		glm::vec4 bottom_right_tr2;
	};

	struct Message_Parent
	{
		unsigned VAO_message, VBO_message, VAO_alphabet, VBO_alphabet;
		unsigned alphabet_texture;

		bool draw_alphabet = true;
		bool dynamic_static = false;

		size_t allocated_memory_bytes = 0;

		int font_size = 10;
		int tallest_font_height = 0;
		int relative_distance = 0;

		int alphabet_texture_width = 0;
		int alphabet_texture_height = 0;

		float alphabet_start_x = -0.80f; // These are set here in OpenGL [-1, 1] coordinate range.
		float alphabet_start_y = -0.45f;

		float text_start_x = 0.0f;
		float text_start_y = 0.0f;

		std::string message_string;
		std::vector<Alphabet_Characters> alphabet_vec;
		Message_Characters alphabet_quad;

		std::vector<Message_Characters> characters_quads;
		std::vector<float> start_x_current;

		std::string font_path;
	};
	// --------------------------------	
	std::string alphabet_string;

	FT_Library& free_type;
	FT_GlyphSlot glyph; // "glyph" (FT_GlyphSlot) is simply being used as shorthand for "face" (FT_Face) ->glyph... set in: set_font_parameters()

	float scale_pixels_x_to_OpenGL = 0.0f; // OpenGL [-1, 1] (i.e. 2) divided by the number of screen pixels.
	float scale_pixels_y_to_OpenGL = 0.0f;

	int character_row_limit = 15; // Alphabet character row limit.
	int alphabet_padding = 7; // Padding is optional (it spaces out the alphabet characters, without affecting each message's character spacing)
	// Note: if character background is slightly opaque e.g. 0.1 = vec4(1, 1, 1, texture(text_Texture, texture_coordinates).r) + 0.1, then spaces, i.e. simply " " show as a: alphabet_padding * alphabet_padding square.

public:
	FT_Face face; // Resources are freed in main() via FT_Done_Face(...)

	std::vector<Message_Parent> messages;

	Text(FT_Library& free_type, int window_width, int window_height, std::string alphabet_string) : free_type(free_type)
	{
		this->alphabet_string = alphabet_string;
		scale_pixels_x_to_OpenGL = 2.0f / window_width; // Scale vertex data to render on-screen the same size as the font's set pixel-size... 
		scale_pixels_y_to_OpenGL = 2.0f / window_height; // This makes the text display at the same correct pixel size, regardless of the window size.
	}

	void create_text_message(std::string message, int text_start_x, int text_start_y, std::string font_path, int font_size, bool dynamic_static)
	{
		int alphabet_detected = -1;
		for (int i = 0; i < messages.size(); ++i)
		{
			if (messages[i].font_size == font_size && messages[i].font_path == font_path)
			{
				alphabet_detected = i;
				break;
			}
		}
		Message_Parent new_message; // Changed by reference during most of the below function calls.

		new_message.font_size = font_size;
		new_message.font_path = font_path;

		if (alphabet_detected == -1) // Create new alphabet.
		{
			std::cout << "\n\n   New alphabet created (characters are listed below) --- Font path: " << font_path << " --- Font size: " << font_size;

			set_font_parameters(new_message);
			create_blank_texture(new_message);
			calculate_alphabet_image_size(new_message);
			format_alphabet_texture_image(new_message);
			create_alphabet_image_quad(new_message);
			set_buffer_data_alphabet(new_message);
		}
		else // Copy the existing alphabet.
		{
			new_message.draw_alphabet = false;
			new_message.alphabet_vec = messages[alphabet_detected].alphabet_vec;
			new_message.alphabet_texture = messages[alphabet_detected].alphabet_texture;
			new_message.alphabet_texture_width = messages[alphabet_detected].alphabet_texture_width;
			new_message.alphabet_texture_height = messages[alphabet_detected].alphabet_texture_height;
			new_message.tallest_font_height = messages[alphabet_detected].tallest_font_height;
			new_message.relative_distance = messages[alphabet_detected].relative_distance;

			std::cout << "\n\n   Existing alphabet detected (no new alphabet is required) --- Font path: " << font_path << " --- Font size: " << font_size << "\n";
		}
		new_message.message_string = message;
		process_text_compare(new_message, text_start_x, text_start_y); // process_text_index(...) is called within this function call.

		new_message.dynamic_static = dynamic_static; // True = dynamic.
		initialise_buffer_data_message(new_message); // Initialise the message's buffer data.
		update_buffer_data_message(new_message, 0); // Update the message's buffer data.

		messages.push_back(new_message); // Add the new message to the list of messages.
	}

	void draw_alphabets()
	{
		for (unsigned i = 0; i < messages.size(); ++i)
		{
			if (messages[i].draw_alphabet)
			{
				glBindVertexArray(messages[i].VAO_alphabet);

				glActiveTexture(GL_TEXTURE31);
				glBindTexture(GL_TEXTURE_2D, messages[i].alphabet_texture);

				glDisable(GL_DEPTH_TEST);
				glDrawArrays(GL_TRIANGLES, 0, 6);
				glEnable(GL_DEPTH_TEST);

				glActiveTexture(GL_TEXTURE0);
				glBindVertexArray(0);
				// std::cout << "\n   Drawing alphabet... messages index: " << i;
			}
		}
	}

	void draw_messages()
	{
		for (unsigned i = 0; i < messages.size(); ++i)
		{
			glBindVertexArray(messages[i].VAO_message);

			glActiveTexture(GL_TEXTURE31);
			glBindTexture(GL_TEXTURE_2D, messages[i].alphabet_texture);

			glDisable(GL_DEPTH_TEST); // Cast (unsigned) used below, silences the compiler warning (unsigned 32 bit is still over 4 billion)
			glDrawArrays(GL_TRIANGLES, 0, (unsigned)messages[i].characters_quads.size() * 6);
			glEnable(GL_DEPTH_TEST);

			glActiveTexture(GL_TEXTURE0);
			glBindVertexArray(0);
		}
	}

	void draw_messages(unsigned message_index)
	{
		if (message_index > messages.size() - 1)
		{
			std::cout << "\n   Warning: draw_messages(...) --- 'message_index' is greater than 'messages.size() - 1'\n";

			int keep_console_open;
			std::cin >> keep_console_open;
		}
		else
		{
			glBindVertexArray(messages[message_index].VAO_message);

			glActiveTexture(GL_TEXTURE31);
			glBindTexture(GL_TEXTURE_2D, messages[message_index].alphabet_texture);

			glDisable(GL_DEPTH_TEST); // Cast (unsigned) used below, silences the compiler warning (unsigned 32 bit is still over 4 billion)
			glDrawArrays(GL_TRIANGLES, 0, (unsigned)messages[message_index].characters_quads.size() * 6);
			glEnable(GL_DEPTH_TEST);

			glActiveTexture(GL_TEXTURE0);
			glBindVertexArray(0);
		}
	}

	void process_text_index(Message_Parent& new_message, unsigned index, float advanced_current)
	{
		// Y-Values (by default the characters are bottom aligned) ("new_message.text_start_x & text_start_y"  are set in: process_text_compare(...))
		// ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
		float bottom_bearing = new_message.alphabet_vec[index].bottom_bearing;
		float y_pos_aligned = new_message.text_start_y - bottom_bearing;
		float height = new_message.alphabet_vec[index].height_plus_padding;

		float texcoord_top_left_y = new_message.alphabet_vec[index].texcoord_top_left.y;
		float texcoord_bottom_right_y = new_message.alphabet_vec[index].texcoord_bottom_right.y;
		float texcoord_top_right_y = new_message.alphabet_vec[index].texcoord_top_right.y;
		float texcoord_bottom_left_y = new_message.alphabet_vec[index].texcoord_bottom_left.y;

		// X-Values
		// -----------		
		float start_x_current = new_message.text_start_x + advanced_current;
		float left_bearing = new_message.alphabet_vec[index].left_bearing;
		float width = new_message.alphabet_vec[index].width_plus_padding;

		float texcoord_bottom_left_x = new_message.alphabet_vec[index].texcoord_bottom_left.x;
		float texcoord_bottom_right_x = new_message.alphabet_vec[index].texcoord_bottom_right.x;
		float texcoord_top_left_x = new_message.alphabet_vec[index].texcoord_top_left.x;
		float texcoord_top_right_x = new_message.alphabet_vec[index].texcoord_top_right.x;

		Message_Characters quad{};

		// Triangle 1
		// -------------
		quad.bottom_left_tr1.x = start_x_current + left_bearing;

		// Used for replacing characters from some index position, to the end of the full message length
		// ---------------------------------------------------------------------------------------------------------------------------
		new_message.start_x_current.push_back(start_x_current); // Record the character's start position... but excluding: left_bearing	

		quad.bottom_left_tr1.y = y_pos_aligned;
		quad.bottom_left_tr1.z = texcoord_bottom_left_x;
		quad.bottom_left_tr1.w = texcoord_top_left_y; // Y-axis texture coordinates are reversed.

		quad.bottom_right_tr1.x = start_x_current + left_bearing + width;
		quad.bottom_right_tr1.y = y_pos_aligned;
		quad.bottom_right_tr1.z = texcoord_bottom_right_x;
		quad.bottom_right_tr1.w = texcoord_top_right_y;

		quad.top_left_tr1.x = start_x_current + left_bearing;
		quad.top_left_tr1.y = y_pos_aligned + height;
		quad.top_left_tr1.z = texcoord_top_left_x;
		quad.top_left_tr1.w = texcoord_bottom_left_y;

		// Triangle 2
		// -------------
		quad.top_left_tr2.x = start_x_current + left_bearing;
		quad.top_left_tr2.y = y_pos_aligned + height;
		quad.top_left_tr2.z = texcoord_top_left_x;
		quad.top_left_tr2.w = texcoord_bottom_left_y;

		quad.top_right_tr2.x = start_x_current + left_bearing + width;
		quad.top_right_tr2.y = y_pos_aligned + height;
		quad.top_right_tr2.z = texcoord_top_right_x;
		quad.top_right_tr2.w = texcoord_bottom_right_y;

		quad.bottom_right_tr2.x = start_x_current + left_bearing + width;
		quad.bottom_right_tr2.y = y_pos_aligned;
		quad.bottom_right_tr2.z = texcoord_bottom_right_x;
		quad.bottom_right_tr2.w = texcoord_top_right_y;
		// --------------------------------------------------------------
		// std::cout << "\n   CHARACTER: " << new_message.message_string.c_str()[index] << " --- start_x_current: " << start_x_current << " --- y_pos_aligned: " << y_pos_aligned << " --- width: " << width << " --- height: " << height;
		// std::cout << "\n  texcoord_top_left_x: " << texcoord_top_left_x;
		// std::cout << "\n   texcoord_top_right_x: " << texcoord_top_right_x << "\n";

		new_message.characters_quads.push_back(quad);
	}

	void update_buffer_data_message(Message_Parent& new_message, int characters_offset)
	{
		glBindVertexArray(new_message.VAO_message);
		glBindBuffer(GL_ARRAY_BUFFER, new_message.VBO_message);

		GLintptr data_offset_bytes = (GLintptr)characters_offset * 6 * 4 * sizeof(float);
		GLsizeiptr replace_size_bytes = (new_message.characters_quads.size() * 6 * 4 * sizeof(float)) - data_offset_bytes;

		if (data_offset_bytes + replace_size_bytes > (unsigned)new_message.allocated_memory_bytes)
		{
			std::cout << "\n   Warning: update_buffer_data_message(...) --- 'data_offset_bytes' " << data_offset_bytes << " + 'replace_size_bytes' " << replace_size_bytes << " was too large for 'allocated_memory_bytes' "
				<< new_message.allocated_memory_bytes << " --- so 'replace_size_bytes' has been reduced to: ";

			replace_size_bytes -= (data_offset_bytes + replace_size_bytes) - new_message.allocated_memory_bytes;
			std::cout << replace_size_bytes;
		}
		if (data_offset_bytes + replace_size_bytes < (unsigned)new_message.allocated_memory_bytes)
		{
			std::cout << "\n   Warning: update_buffer_data_message(...) --- 'data_offset_bytes' " << data_offset_bytes << " + 'replace_size_bytes' " << replace_size_bytes << " is less than 'allocated_memory_bytes' "
				<< new_message.allocated_memory_bytes << " --- so 'characters_offset' " << characters_offset << " has been reduced to: ";

			characters_offset -= (int)((new_message.allocated_memory_bytes - (data_offset_bytes + replace_size_bytes)) / 6 / 4 / sizeof(float));
			std::cout << characters_offset;
		}
		int keep_console_open;
		if (characters_offset == -1)
			std::cin >> keep_console_open;

		glBufferSubData(GL_ARRAY_BUFFER, data_offset_bytes, replace_size_bytes, &new_message.characters_quads[characters_offset]);
		glBindVertexArray(0);
	}

private:
	void set_font_parameters(Message_Parent new_message)
	{
		FT_Error error_code{};
		int keep_console_open;

		error_code = FT_New_Face(free_type, new_message.font_path.c_str(), 0, &face);
		if (error_code)
		{
			std::cout << "\n\n   Error code: " << error_code << " --- " << "Could not open font: " << new_message.font_path.c_str();
			std::cin >> keep_console_open;
		}
		error_code = FT_Set_Pixel_Sizes(face, 0, new_message.font_size);
		if (error_code)
		{
			std::cout << "\n\n   Error code: " << error_code << " --- " << "Could not set font pixel size : " << new_message.font_size;
			std::cin >> keep_console_open;
		}
		glyph = face->glyph; // Shorthand for "face->glyph"
	}

	void create_blank_texture(Message_Parent& new_message)
	{
		glGenTextures(1, &new_message.alphabet_texture);
		glActiveTexture(GL_TEXTURE31);
		glBindTexture(GL_TEXTURE_2D, new_message.alphabet_texture);

		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);

		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST); // GL_NEAREST... GL_LINEAR
		glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);

		glActiveTexture(GL_TEXTURE0);
	}

	void calculate_alphabet_image_size(Message_Parent& new_message)
	{
		FT_Error error_code{};

		int curr_row_width = 0;
		int max_row_width = 0;
		int number_of_rows = 1;
		int character_count = 0;

		new_message.tallest_font_height = 0;

		for (unsigned i = 0; i < alphabet_string.size(); i++)
		{
			error_code = FT_Load_Char(face, alphabet_string[i], FT_LOAD_RENDER);
			if (error_code)
			{
				std::cout << "\n\n   Error code: " << error_code << " --- " << "Could not load character: " << alphabet_string[i];
				int keep_console_open;
				std::cin >> keep_console_open;
			}
			if ((signed)glyph->bitmap.rows > new_message.tallest_font_height)
				new_message.tallest_font_height = glyph->bitmap.rows;

			curr_row_width += glyph->bitmap.width + alphabet_padding * 2;

			++character_count;
			if (character_count == character_row_limit)
			{
				character_count = 0;
				++number_of_rows;

				if (curr_row_width > max_row_width)
					max_row_width = curr_row_width;

				curr_row_width = 0;
			}
			new_message.alphabet_texture_width = (curr_row_width > max_row_width) ? curr_row_width : max_row_width;
			// std::cout << "\n\n   alphabet_texture_width: " << alphabet_texture_width;
		}
		new_message.alphabet_texture_height = number_of_rows * (new_message.tallest_font_height + alphabet_padding * 2);

		std::cout << "\n\n   alphabet_texture_width: " << new_message.alphabet_texture_width
			<< " --- alphabet_texture_height: " << new_message.alphabet_texture_height << "\n";
	}

	void format_alphabet_texture_image(Message_Parent& new_message)
	{
		glActiveTexture(GL_TEXTURE31);
		glBindTexture(GL_TEXTURE_2D, new_message.alphabet_texture);

		glPixelStorei(GL_UNPACK_ALIGNMENT, 1);

		// Initialise empty data: https://stackoverflow.com/questions/7195130/how-to-efficiently-initialize-texture-with-zeroes
		std::vector<GLubyte> empty_data(new_message.alphabet_texture_width * new_message.alphabet_texture_height, 0); // GL_RED = 8 bits = 1 byte.

		//  https://www.khronos.org/registry/OpenGL-Refpages/gl4/html/glTexImage2D.xhtml
		// "Each element is a single red component. OpenGL converts it to floating point and assembles it to RGBA, by attaching 0 for green and blue, and 1 for alpha. Each component is clamped to the range [0, 1]"
		glTexImage2D(GL_TEXTURE_2D, 0, GL_RED, new_message.alphabet_texture_width, new_message.alphabet_texture_height, 0, GL_RED, GL_UNSIGNED_BYTE, &empty_data[0]);

		int character_count = 0;
		int increment_x = alphabet_padding;
		int increment_y = alphabet_padding;

		new_message.relative_distance = new_message.tallest_font_height; // Set relative distance to initial value.

		for (unsigned i = 0; i < alphabet_string.size(); ++i)
		{
			FT_Load_Char(face, alphabet_string[i], FT_LOAD_RENDER); // "glyph" as used below... is shorthand for "face->glyph"

			int tex_coord_left = increment_x - alphabet_padding;
			glTexSubImage2D(GL_TEXTURE_2D, 0, increment_x, increment_y, glyph->bitmap.width, glyph->bitmap.rows, GL_RED, GL_UNSIGNED_BYTE, glyph->bitmap.buffer); // Apply 1 character at a time to the texture.
			int tex_coord_right = increment_x + glyph->bitmap.width + alphabet_padding;

			int tex_coord_bottom = increment_y - alphabet_padding;
			int tex_coord_top = increment_y + glyph->bitmap.rows + alphabet_padding;

			increment_x += glyph->bitmap.width + (alphabet_padding * 2);

			// By default the characters are bottom aligned (Note: bitmap_top = the "Remaining Distance" above that bottom alignment, after having been moved downwards by "bottom_bearing" to produce character-origin alignment)
			// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
			if (new_message.relative_distance > new_message.tallest_font_height - glyph->bitmap_top)
				new_message.relative_distance = new_message.tallest_font_height - glyph->bitmap_top; // Record the smallest... Tallest Font - "Remaining Distance" (incidentally, the tallest font is also checked against itself by doing this)

			// FT_GlyphSlotRec: https://freetype.org/freetype2/docs/reference/ft2-base_interface.html#ft_glyphslotrec (Also available: https://freetype.org/freetype2/docs/reference/ft2-base_interface.html#ft_glyph_metrics)
			// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
			Alphabet_Characters alphabet_character{};
			alphabet_character.glyph_advance_x = (glyph->advance.x / 64) * scale_pixels_x_to_OpenGL;

			// The values below are in pixels...  FT_Bitmap: https://freetype.org/freetype2/docs/reference/ft2-basic_types.html#ft_bitmap			
			// --------------------------------------------------------------------------------------------------------------------------------------------------------------------		
			alphabet_character.left_bearing = glyph->bitmap_left * scale_pixels_x_to_OpenGL;
			alphabet_character.width_plus_padding = (tex_coord_right - tex_coord_left) * scale_pixels_x_to_OpenGL;
			alphabet_character.bottom_bearing = ((int)glyph->bitmap.rows - (int)glyph->bitmap_top) * scale_pixels_y_to_OpenGL;
			alphabet_character.height_plus_padding = (tex_coord_top - tex_coord_bottom) * scale_pixels_y_to_OpenGL;
			alphabet_character.character = alphabet_string[i];

			std::cout << "\n   CHARACTER: " << alphabet_string[i] << "\n   glyph->advance.x: " << glyph->advance.x << "\n   glyph->advance.x / 64: " << glyph->advance.x / 64
				<< "\n   glyph->bitmap_left: " << glyph->bitmap_left << "\n   glyph->bitmap.width: " << glyph->bitmap.width << "\n   glyph->bitmap.rows: " << glyph->bitmap.rows
				<< "\n   bottom bearing (height - top): " << (int)glyph->bitmap.rows - (int)glyph->bitmap_top << "\n   top bearing (bitmap_top): " << glyph->bitmap_top << "\n";

			// Texture Coordinates Section (divide texture coordinate position values by texture size to get range [0, 1])
			// ------------------------------------------------------------------------------------------------------------------------------------------
			alphabet_character.texcoord_top_left.x = (float)tex_coord_left / (float)new_message.alphabet_texture_width;
			alphabet_character.texcoord_top_left.y = (float)(tex_coord_top) / (float)new_message.alphabet_texture_height;

			alphabet_character.texcoord_top_right.x = (float)(tex_coord_right) / (float)new_message.alphabet_texture_width;
			alphabet_character.texcoord_top_right.y = (float)(tex_coord_top) / (float)new_message.alphabet_texture_height;

			alphabet_character.texcoord_bottom_left.x = (float)(tex_coord_left) / (float)new_message.alphabet_texture_width;
			alphabet_character.texcoord_bottom_left.y = (float)(tex_coord_bottom) / (float)new_message.alphabet_texture_height;

			alphabet_character.texcoord_bottom_right.x = (float)(tex_coord_right) / (float)new_message.alphabet_texture_width;
			alphabet_character.texcoord_bottom_right.y = (float)(tex_coord_bottom) / (float)new_message.alphabet_texture_height;

			new_message.alphabet_vec.push_back(alphabet_character); // Used in: process_text_compare()

			++character_count;
			if (character_count == character_row_limit)
			{
				character_count = 0;
				increment_y += new_message.tallest_font_height + (alphabet_padding * 2);
				increment_x = alphabet_padding;
			}
		}
		glActiveTexture(GL_TEXTURE0);
	}

	void create_alphabet_image_quad(Message_Parent& new_message)
	{
		float x = new_message.alphabet_start_x;
		float y = new_message.alphabet_start_y;

		float width = new_message.alphabet_texture_width * scale_pixels_x_to_OpenGL;
		float height = new_message.alphabet_texture_height * scale_pixels_y_to_OpenGL;

		float margin = 50 * scale_pixels_x_to_OpenGL; // Display each alphabet to the right of the previous one.
		if (messages.size() > 0)
		{
			x = messages[messages.size() - 1].alphabet_start_x + (messages[messages.size() - 1].alphabet_texture_width * scale_pixels_x_to_OpenGL) + margin;
			new_message.alphabet_start_x = x;
		}
		// Triangle 1
		// -------------
		new_message.alphabet_quad.bottom_left_tr1.x = x;
		new_message.alphabet_quad.bottom_left_tr1.y = y;
		new_message.alphabet_quad.bottom_left_tr1.z = 0.0f;
		new_message.alphabet_quad.bottom_left_tr1.w = 1.0f;

		new_message.alphabet_quad.bottom_right_tr1.x = x + width;
		new_message.alphabet_quad.bottom_right_tr1.y = y;
		new_message.alphabet_quad.bottom_right_tr1.z = 1.0f;
		new_message.alphabet_quad.bottom_right_tr1.w = 1.0f;

		new_message.alphabet_quad.top_left_tr1.x = x;
		new_message.alphabet_quad.top_left_tr1.y = y + height;
		new_message.alphabet_quad.top_left_tr1.z = 0.0f;
		new_message.alphabet_quad.top_left_tr1.w = 0.0f;

		// Triangle 2
		// -------------
		new_message.alphabet_quad.top_left_tr2.x = x;
		new_message.alphabet_quad.top_left_tr2.y = y + height;
		new_message.alphabet_quad.top_left_tr2.z = 0.0f;
		new_message.alphabet_quad.top_left_tr2.w = 0.0f;

		new_message.alphabet_quad.top_right_tr2.x = x + width;
		new_message.alphabet_quad.top_right_tr2.y = y + height;
		new_message.alphabet_quad.top_right_tr2.z = 1.0f;
		new_message.alphabet_quad.top_right_tr2.w = 0.0f;

		new_message.alphabet_quad.bottom_right_tr2.x = x + width;
		new_message.alphabet_quad.bottom_right_tr2.y = y;
		new_message.alphabet_quad.bottom_right_tr2.z = 1.0f;
		new_message.alphabet_quad.bottom_right_tr2.w = 1.0f;
	}

	void set_buffer_data_alphabet(Message_Parent& new_message)
	{
		glGenVertexArrays(1, &new_message.VAO_alphabet);
		glGenBuffers(1, &new_message.VBO_alphabet);

		glBindVertexArray(new_message.VAO_alphabet);
		glBindBuffer(GL_ARRAY_BUFFER, new_message.VBO_alphabet);

		glBufferData(GL_ARRAY_BUFFER, 6 * 4 * sizeof(float), &new_message.alphabet_quad, GL_STATIC_DRAW);

		glEnableVertexAttribArray(0);
		glVertexAttribPointer(0, 4, GL_FLOAT, GL_FALSE, 0, (void*)0);

		glBindVertexArray(0);
	}

	void process_text_compare(Message_Parent& new_message, int text_start_x, int text_start_y)
	{
		float advance_to_next_character = 0.0f;

		// "relative_distance" and "tallest_character" are fixed values, calculated per message (used here to align the text's highest pixel to the display window's top row of pixels)
		float tallest_character = new_message.tallest_font_height * scale_pixels_y_to_OpenGL;
		float relative_distance = new_message.relative_distance * scale_pixels_y_to_OpenGL;

		for (unsigned i = 0; i < new_message.message_string.size(); ++i)
		{
			for (unsigned i2 = 0; i2 < new_message.alphabet_vec.size(); ++i2)
			{
				if (new_message.message_string.c_str()[i] == new_message.alphabet_vec[i2].character)
				{
					if (advance_to_next_character == 0) // Start X, Y positions need setting here, but only for the 1st character, i.e. when: advance_to_next_character = 0
					{
						// Enable these two lines for 2D window-positioned text
						// -----------------------------------------------------------------------
						new_message.text_start_x = -1.0f - new_message.alphabet_vec[i2].left_bearing + (text_start_x - alphabet_padding) * scale_pixels_x_to_OpenGL;
						new_message.text_start_y = 1.0f + relative_distance - tallest_character - (text_start_y + alphabet_padding) * scale_pixels_y_to_OpenGL;

						// Enable these two lines instead for 3D animated text
						// --------------------------------------------------------------------
						// new_message.text_start_x = -1.35f;
						// new_message.text_start_y = 0.0f;
					}
					process_text_index(new_message, i2, advance_to_next_character);
					advance_to_next_character += new_message.alphabet_vec[i2].glyph_advance_x;

					break; // Stop checking the alphabet if the character is found.
				}
			}
		}
	}

	void initialise_buffer_data_message(Message_Parent& new_message)
	{
		glGenVertexArrays(1, &new_message.VAO_message);
		glGenBuffers(1, &new_message.VBO_message);

		glBindVertexArray(new_message.VAO_message);
		glBindBuffer(GL_ARRAY_BUFFER, new_message.VBO_message);

		new_message.allocated_memory_bytes = new_message.characters_quads.size() * 6 * 4 * sizeof(float);

		if (new_message.dynamic_static)
			glBufferData(GL_ARRAY_BUFFER, new_message.allocated_memory_bytes, NULL, GL_DYNAMIC_DRAW);
		else
			glBufferData(GL_ARRAY_BUFFER, new_message.allocated_memory_bytes, NULL, GL_STATIC_DRAW);

		glEnableVertexAttribArray(0);
		glVertexAttribPointer(0, 4, GL_FLOAT, GL_FALSE, 0, (void*)0);

		glBindVertexArray(0);
	}
};
