#pragma once // Instead of using include guards.

class Shader
{
public:
	GLuint ID; // Public Program ID.

	// Constructor
	// ---------------
	Shader(const char* vert_path, const char* frag_path)
	{
		char character;

		std::ifstream vert_stream;
		std::ifstream frag_stream;

		std::string vert_string;
		std::string frag_string;

		// Read vertex shader text file
		// ------------------------------------
		vert_stream.open(vert_path); // I decided not to implement: Exception handling try catch method.

		if (vert_stream.is_open()) // Note: There are various other methods for accessing the stream, i.e., vert_stream.get() is just one option.
		{
			while (vert_stream.get(character)) // Loop getting single characters until EOF (value false) is returned. 
				vert_string += character; // "The first signature returns the character read, or the end-of-file value (EOF) if no characters are available in the stream..."

			vert_stream.close();
			std::cout << "\n   File: " << vert_path << " opened successfully.\n\n";
		}
		else
			std::cout << "   ERROR!... File: " << vert_path << " could not be opened.\n\n";

		// Read fragment shader text file
		// ----------------------------------------
		frag_stream.open(frag_path);

		if (frag_stream.is_open())
		{
			while (frag_stream.get(character))
				frag_string += character;

			frag_stream.close();
			std::cout << "   File: " << frag_path << " opened successfully.\n\n";
		}
		else
			std::cout << "   ERROR!... File: " << frag_path << " could not be opened.\n\n";

		// std::cout << vert_string << "\n\n"; // Output the shader files to display in the console window.
		// std::cout << frag_string << "\n\n";

		const char* vert_pointer = vert_string.c_str();
		const char* frag_pointer = frag_string.c_str();

		// Compile shaders
		// ----------------------
		GLuint vert_shad, frag_shad; // Declare in here locally. Being attached to the public Program ID allows the shaders to be used publicly.

		// Create vertex shader
		// ---------------------------
		vert_shad = glCreateShader(GL_VERTEX_SHADER);
		glShaderSource(vert_shad, 1, &vert_pointer, NULL);
		glCompileShader(vert_shad);
		Check_Shaders_Program(vert_shad, "vert_shader");

		// Create fragment shader
		// -------------------------------
		frag_shad = glCreateShader(GL_FRAGMENT_SHADER);
		glShaderSource(frag_shad, 1, &frag_pointer, NULL);
		glCompileShader(frag_shad);
		Check_Shaders_Program(frag_shad, "frag_shader");

		// Create shader program
		// ------------------------------
		ID = glCreateProgram();
		glAttachShader(ID, vert_shad); // This also avoids deletion via: glDeleteShader(vert_shad) as called below.
		glAttachShader(ID, frag_shad);
		glLinkProgram(ID);
		Check_Shaders_Program(ID, "shader_program");

		// Note: Flagging the program object for deletion before calling "glUseProgram" would accidentally stop the program installation of the rendering state	
		// ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
		glDeleteShader(vert_shad); // Flag shader object for automatic deletion (freeing memory) when no longer attached to a program object...
		glDeleteShader(frag_shad); // ... program object is deleted (glDeleteProgram ) within: main() when the application ends.

		// glUseProgram(ID); // Typically this is called within: main() to select individual shaders that have been created. 
		// glDeleteProgram(ID); // Alternatively the program object can be deleted here after 1st calling:  glUseProgram(ID)
	}

	// Activate the shader
	// -------------------------
	void use()
	{
		glUseProgram(ID); // Function called from within main() to select an individual shader to be used.
	}

private:
	// Check shader compilations and program object for linking errors
	// -------------------------------------------------------------------------------------
	void Check_Shaders_Program(GLuint type, std::string name)
	{
		int success;
		int error_log_size;
		char info_log[1000]; // 1000 characters max. Typically it's less than 500 even for multiple shader errors.

		if (name == "vert_shader" || name == "frag_shader")
		{
			glGetShaderiv(type, GL_COMPILE_STATUS, &success);
			if (!success)
			{
				glGetShaderInfoLog(type, 1024, &error_log_size, info_log);
				std::cout << "\n--- Shader Compilation Error: " << name << "\n\n" << info_log << "\n" << "Error Log Number of Characters: " << error_log_size << "\n\n";
			}
		}
		else // "shader_program"
		{
			glGetProgramiv(type, GL_LINK_STATUS, &success);
			if (!success)
			{
				glGetProgramInfoLog(type, 1024, &error_log_size, info_log);
				std::cout << "\n--- Program Link Error: " << name << "\n\n" << info_log << "\n" << "Error Log Number of Characters: " << error_log_size << "\n";
			}
		}
	}
};