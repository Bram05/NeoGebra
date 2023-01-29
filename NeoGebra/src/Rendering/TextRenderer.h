// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include <glad/glad.h>
#include "Shader.h"
#include "Maths/Equation.h"

// Simple struct with the general information for a character
struct CharacterInfo
{
	int x, y;
	int width, height;
	int xOffset, yOffset;
	int xAdvance;
	int page;
	int channel;
};

// A font to be used for rendering text
class Font
{
public:
	// Loads the font with this name. Name has to be the name of the folder within 'assets/fonts'
	Font(const std::string& fontName);
	~Font();

	// Get the info for this charater loaded from the font
	// @param character: the unicode point for the character. It will change this value to be ? if the character is not found
	CharacterInfo GetCharacterInfo(unsigned int& character);
	int GetWidth() const { return m_TotalWidth; }
	int GetHeight() const { return m_TotalHeight; }
	GLuint GetBitmap() const { return m_Bitmap; }
	int GetSize() const { return m_Size; }
	int GetLineHeight() const { return m_LineHeight; }
	int GetBase() const { return m_Base; }

private:
	GLuint m_Bitmap;
	std::map<int, CharacterInfo> m_CharacterInformation;
	int m_LineHeight, m_Base;
	int m_Size;
	int m_TotalWidth, m_TotalHeight;
	std::string m_BaseFont;
};

class TextRenderer;

// Text object to be rendered
class Text
{
public:
	// Constructor
	// @param renderAllText: should all the text be rendered, or only the part between m_RenderBegin and m_RenderEnd
	Text(const AdvancedString& letters, float leftX, float rightX, float baseLine, float size, bool renderAllText = true, const std::array<float, 4>& colour = { 0.0f,0.0f,0.0f,1.0f });
	Text(const std::string& text, float leftX, float rightX, float baseLine, float size, bool renderAllText = true, const std::array<float, 4>& colour = { 0.0f,0.0f,0.0f,1.0f });
	~Text();

	void AddText(const AdvancedString& letters, int position);
	void AddText(const std::string& letters, int position);
	void SetText(const AdvancedString& text);
	void SetText(const std::string& text);
	void RemoveText(int begin, int num);

	const AdvancedString& GetText() const { return m_Text; }
	AdvancedString& GetText() { return m_Text; }
	float GetScale() const { return m_Scale; }

	// The first and last letter of the text that needs to be rendered. RenderEnd is one beyond the last rendered character
	// This is only used if m_RenderAllText is false
	int m_RenderBegin, m_RenderEnd;
	std::array<float, 4> m_Colour;

private:
	bool m_RenderAllText;
	float m_Size;
	AdvancedString m_Text;
	float m_LeftX, m_RightX, m_Baseline;
	float m_Scale;
	friend TextRenderer;
};

// Underlying text rendererer
class TextRenderer
{
public:
	// Create the renderer with this specific font. Name has to be the name of the folder withing 'assets/fonts'
	TextRenderer(const std::string& fontName);
	~TextRenderer();

	void AddToRenderQueue(const std::shared_ptr<Text>& m_Text);
	void RenderQueue(int width, int height);

	std::shared_ptr<Font> GetFont() { return m_Font; }

private:
	std::shared_ptr<Font> m_Font;
	GLuint m_Vao, m_Vb, m_Ib;
	std::queue<std::shared_ptr<Text>> m_RenderQueue{};
	Shader m_TextShader;
};